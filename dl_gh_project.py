#!/usr/bin/env python3
"""
Export the issue, comment, and timeline history of a GitHub Projects v2 board to Markdown.

Usage:
    ./dl_gh_project.py --project PROJECT_URL --output OUTPUT.md
    ./dl_gh_project.py -p PROJECT_URL -o OUTPUT.md

Authentication:
    Set GITHUB_TOKEN or GH_TOKEN in the environment. If neither is set, the
    script interactively prompts for a token. For private projects or
    repositories, the token needs permission to read the project and the
    referenced issues / pull requests.

Notes:
    - This script uses only the Python standard library.
    - It supports modern Projects v2 URLs:
        https://github.com/orgs/OWNER/projects/NUMBER
        https://github.com/users/OWNER/projects/NUMBER
        https://github.com/orgs/OWNER/projects/NUMBER/views/VIEW_NUMBER
    - It exports issue opening posts, issue comments, and issue / pull-request timeline events.
    - It exports draft project items as draft-only sections with their bodies.
    - It also exports issue sub-issues as peer Markdown sections after their parent issue.
    - It does not export pull-request review comments.
"""

from __future__ import annotations

import argparse
import getpass
import json
import os
import re
import sys
from collections import OrderedDict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Iterator
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urlencode, urlparse
from urllib.request import Request, urlopen
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

from tqdm import tqdm

API_VERSION = "2026-03-10"
GRAPHQL_URL = "https://api.github.com/graphql"
REST_BASE_URL = "https://api.github.com"
DEFAULT_TZ = "UTC"
USER_AGENT = "dl-gh-project-v2/1.5"
ARCHIVED_COLUMN_NAME = "Archived"
ARCHIVED_SECTION_KEY = "__dl_gh_project_archived_items__"
ARCHIVED_FROM_COLUMN_KEY = "_dl_gh_project_archived_from_column"
SUB_ISSUE_PARENT_TITLE_KEY = "_dl_gh_project_sub_issue_parent_title"
SUB_ISSUE_PARENT_KEY_KEY = "_dl_gh_project_sub_issue_parent_key"


class GitHubAPIError(RuntimeError):
    """Raised when GitHub returns an API error or the API response is invalid."""


@dataclass(frozen=True)
class ProjectURL:
    scope: str  # "orgs" or "users"
    owner: str
    number: int
    view_number: int | None


PROJECT_QUERY = """
query($owner: String!, $number: Int!, $isOrg: Boolean!) {
  organization(login: $owner) @include(if: $isOrg) {
    projectV2(number: $number) {
      ...ProjectInfo
    }
  }

  user(login: $owner) @skip(if: $isOrg) {
    projectV2(number: $number) {
      ...ProjectInfo
    }
  }
}

fragment ProjectInfo on ProjectV2 {
  id
  title
  number
  url

  views(first: 100, orderBy: {field: POSITION, direction: ASC}) {
    nodes {
      id
      number
      name
      layout
      filter

      groupByFields(first: 10, orderBy: {field: POSITION, direction: ASC}) {
        nodes {
          __typename
          ... on ProjectV2FieldCommon {
            id
            name
            dataType
          }
        }
      }

      verticalGroupByFields(first: 10, orderBy: {field: POSITION, direction: ASC}) {
        nodes {
          __typename
          ... on ProjectV2FieldCommon {
            id
            name
            dataType
          }
        }
      }
    }
  }

  fields(first: 100, orderBy: {field: POSITION, direction: ASC}) {
    nodes {
      __typename

      ... on ProjectV2FieldCommon {
        id
        name
        dataType
      }

      ... on ProjectV2SingleSelectField {
        options {
          id
          name
        }
      }

      ... on ProjectV2IterationField {
        configuration {
          iterations {
            id
            title
            startDate
          }
        }
      }
    }
  }
}
"""


ITEMS_QUERY = """
query(
  $projectId: ID!,
  $cursor: String,
  $columnFieldName: String!,
  $archivedStates: [ProjectV2ItemArchivedState!]!
) {
  node(id: $projectId) {
    ... on ProjectV2 {
      items(
        first: 50,
        after: $cursor,
        archivedStates: $archivedStates,
        orderBy: {field: POSITION, direction: ASC}
      ) {
        pageInfo {
          hasNextPage
          endCursor
        }

        nodes {
          id
          type
          isArchived
          createdAt
          updatedAt
          creator {
            login
          }

          columnValue: fieldValueByName(name: $columnFieldName) {
            __typename

            ... on ProjectV2ItemFieldSingleSelectValue {
              name
            }

            ... on ProjectV2ItemFieldIterationValue {
              title
              startDate
              duration
            }

            ... on ProjectV2ItemFieldTextValue {
              text
            }

            ... on ProjectV2ItemFieldNumberValue {
              number
            }

            ... on ProjectV2ItemFieldDateValue {
              date
            }
          }

          content {
            __typename

            ... on Issue {
              id
              number
              title
              body
              url
              state
              createdAt
              updatedAt
              closedAt
              author {
                login
              }
              repository {
                name
                nameWithOwner
                owner {
                  login
                }
              }
            }

            ... on PullRequest {
              id
              number
              title
              body
              url
              state
              createdAt
              updatedAt
              closedAt
              author {
                login
              }
              repository {
                name
                nameWithOwner
                owner {
                  login
                }
              }
            }

            ... on DraftIssue {
              id
              title
              body
              createdAt
              updatedAt
              creator {
                login
              }
            }
          }
        }
      }
    }
  }
}
"""


PROJECT_V2_TIMELINE_QUERY = """
query($contentId: ID!, $cursor: String) {
  node(id: $contentId) {
    __typename

    ... on Issue {
      timelineItems(
        first: 100,
        after: $cursor,
        itemTypes: [
          ADDED_TO_PROJECT_V2_EVENT,
          PROJECT_V2_ITEM_STATUS_CHANGED_EVENT,
          REMOVED_FROM_PROJECT_V2_EVENT,
          CONVERTED_FROM_DRAFT_EVENT
        ]
      ) {
        pageInfo {
          hasNextPage
          endCursor
        }
        nodes {
          __typename

          ... on AddedToProjectV2Event {
            id
            actor {
              login
            }
            createdAt
            project {
              title
              number
              url
            }
            wasAutomated
          }

          ... on ProjectV2ItemStatusChangedEvent {
            id
            actor {
              login
            }
            createdAt
            previousStatus
            status
            project {
              title
              number
              url
            }
            wasAutomated
          }

          ... on RemovedFromProjectV2Event {
            id
            actor {
              login
            }
            createdAt
            project {
              title
              number
              url
            }
            wasAutomated
          }

          ... on ConvertedFromDraftEvent {
            id
            actor {
              login
            }
            createdAt
            project {
              title
              number
              url
            }
            wasAutomated
          }
        }
      }
    }

    ... on PullRequest {
      timelineItems(
        first: 100,
        after: $cursor,
        itemTypes: [
          ADDED_TO_PROJECT_V2_EVENT,
          PROJECT_V2_ITEM_STATUS_CHANGED_EVENT,
          REMOVED_FROM_PROJECT_V2_EVENT,
          CONVERTED_FROM_DRAFT_EVENT
        ]
      ) {
        pageInfo {
          hasNextPage
          endCursor
        }
        nodes {
          __typename

          ... on AddedToProjectV2Event {
            id
            actor {
              login
            }
            createdAt
            project {
              title
              number
              url
            }
            wasAutomated
          }

          ... on ProjectV2ItemStatusChangedEvent {
            id
            actor {
              login
            }
            createdAt
            previousStatus
            status
            project {
              title
              number
              url
            }
            wasAutomated
          }

          ... on RemovedFromProjectV2Event {
            id
            actor {
              login
            }
            createdAt
            project {
              title
              number
              url
            }
            wasAutomated
          }

          ... on ConvertedFromDraftEvent {
            id
            actor {
              login
            }
            createdAt
            project {
              title
              number
              url
            }
            wasAutomated
          }
        }
      }
    }
  }
}
"""

def fine_grained_token_url(project_url: ProjectURL) -> str:
    params = {
        "name": "dl-gh-project",
        "description": "Export GitHub Project issue comments and timeline events to Markdown",
        "expires_in": "30",
        "metadata": "read",
        "issues": "read",
        "pull_requests": "read",
    }

    if project_url.scope == "orgs":
        params["target_name"] = project_url.owner
        params["organization_projects"] = "read"

    return "https://github.com/settings/personal-access-tokens/new?" + urlencode(params)


def classic_token_url() -> str:
    params = {
        "description": "dl-gh-project",
        "scopes": "read:project,repo",
    }
    return "https://github.com/settings/tokens/new?" + urlencode(params)


def token_prompt_instructions(project_url: ProjectURL) -> str:
    classic_url = classic_token_url()

    if project_url.scope == "orgs":
        recommended = (
            "Recommended option for this organization-owned Project:\n"
            f"  1. Open: {fine_grained_token_url(project_url)}\n"
            f"  2. Select resource owner: {project_url.owner}\n"
            "  3. Select the repositories containing the Project's issue / PR cards.\n"
            "  4. Confirm read permissions for Metadata, Issues, Pull requests, and Organization Projects.\n"
        )
        fallback = (
            "Fallback classic-token option:\n"
            f"  1. Open: {classic_url}\n"
            "  2. Select read:project and repo. For public-only repository comments, public_repo may be enough instead of repo.\n"
        )
    else:
        recommended = (
            "Recommended option for this user-owned Project:\n"
            f"  1. Open: {classic_url}\n"
            "  2. Select read:project and repo. For public-only repository comments, public_repo may be enough instead of repo.\n"
        )
        fallback = (
            "Fine-grained personal access tokens are more limited for user-owned Projects;\n"
            "use the classic-token option above if fine-grained project access fails.\n"
        )

    return (
        "No GitHub token was found in GITHUB_TOKEN or GH_TOKEN.\n\n"
        "This script needs a token that can read the GitHub Project and the referenced issue / PR comments and timeline events.\n\n"
        f"{recommended}\n"
        f"{fallback}\n"
        "To avoid this prompt later, run one of these before calling the script:\n"
        "  export GITHUB_TOKEN='paste-token-here'\n"
        "  export GH_TOKEN='paste-token-here'\n\n"
        "Paste the token below. It will not be displayed, written to disk, or exported to your shell."
    )


def get_github_token(project_url: ProjectURL) -> str:
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if token and token.strip():
        return token.strip()

    print(token_prompt_instructions(project_url), file=sys.stderr)
    print("", file=sys.stderr)

    try:
        token = getpass.getpass("GitHub token: ").strip()
    except (EOFError, KeyboardInterrupt) as exc:
        raise GitHubAPIError(
            "GitHub token prompt was cancelled; set GITHUB_TOKEN or GH_TOKEN "
            "in the environment and try again"
        ) from exc

    if not token:
        raise GitHubAPIError(
            "no token entered; set GITHUB_TOKEN or GH_TOKEN in the environment "
            "or rerun and paste a token at the prompt"
        )

    return token


class GitHubClient:
    def __init__(self, token: str) -> None:
        self.token = token

    def _headers(self, *, json_content: bool = False) -> dict[str, str]:
        headers = {
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {self.token}",
            "User-Agent": USER_AGENT,
            "X-GitHub-Api-Version": API_VERSION,
        }
        if json_content:
            headers["Content-Type"] = "application/json"
        return headers

    def _request_json(
        self,
        method: str,
        url: str,
        *,
        params: dict[str, Any] | None = None,
        body: dict[str, Any] | None = None,
    ) -> tuple[Any, Any]:
        if url.startswith("/"):
            url = REST_BASE_URL + url

        if params:
            separator = "&" if "?" in url else "?"
            url = url + separator + urlencode(params, doseq=True)

        encoded_body = None
        if body is not None:
            encoded_body = json.dumps(body).encode("utf-8")

        request = Request(
            url,
            data=encoded_body,
            headers=self._headers(json_content=body is not None),
            method=method,
        )

        try:
            with urlopen(request, timeout=60) as response:
                raw = response.read().decode("utf-8")
                if not raw:
                    return None, response.headers
                return json.loads(raw), response.headers
        except HTTPError as exc:
            raw = exc.read().decode("utf-8", errors="replace")
            message = self._format_http_error(method, url, exc, raw)
            raise GitHubAPIError(message) from exc
        except URLError as exc:
            raise GitHubAPIError(f"{method} {url} failed: {exc.reason}") from exc
        except json.JSONDecodeError as exc:
            raise GitHubAPIError(f"{method} {url} returned invalid JSON") from exc

    def _format_http_error(self, method: str, url: str, exc: HTTPError, raw: str) -> str:
        parts = [f"{method} {url} failed: HTTP {exc.code}"]

        try:
            payload = json.loads(raw)
            if isinstance(payload, dict):
                if payload.get("message"):
                    parts.append(str(payload["message"]))
                if payload.get("errors"):
                    parts.append(json.dumps(payload["errors"], indent=2))
            elif raw:
                parts.append(raw)
        except json.JSONDecodeError:
            if raw:
                parts.append(raw)

        rate_remaining = exc.headers.get("X-RateLimit-Remaining")
        rate_reset = exc.headers.get("X-RateLimit-Reset")
        if rate_remaining == "0" and rate_reset:
            parts.append(f"GitHub API rate limit reset epoch: {rate_reset}")

        return "\n".join(parts)

    def graphql(self, query: str, variables: dict[str, Any]) -> dict[str, Any]:
        payload, _headers = self._request_json(
            "POST",
            GRAPHQL_URL,
            body={"query": query, "variables": variables},
        )

        if not isinstance(payload, dict):
            raise GitHubAPIError("GraphQL response was not a JSON object")

        if payload.get("errors"):
            raise GitHubAPIError(json.dumps(payload["errors"], indent=2))

        data = payload.get("data")
        if not isinstance(data, dict):
            raise GitHubAPIError("GraphQL response did not contain a data object")

        return data

    def rest_get_paginated(
        self,
        path: str,
        *,
        params: dict[str, Any] | None = None,
    ) -> Iterator[Any]:
        url: str | None = path
        current_params = params

        while url:
            payload, headers = self._request_json("GET", url, params=current_params)

            if isinstance(payload, list):
                yield from payload
            elif payload is not None:
                yield payload

            url = parse_next_link(headers.get("Link"))
            current_params = None


def parse_next_link(link_header: str | None) -> str | None:
    if not link_header:
        return None

    for part in link_header.split(","):
        part = part.strip()
        match = re.match(r'<([^>]+)>;\s*rel="next"', part)
        if match:
            return match.group(1)

        pieces = [piece.strip() for piece in part.split(";")]
        if len(pieces) >= 2 and 'rel="next"' in pieces[1:]:
            url_part = pieces[0]
            if url_part.startswith("<") and url_part.endswith(">"):
                return url_part[1:-1]

    return None


def parse_project_url(project_url: str) -> ProjectURL:
    parsed = urlparse(project_url)

    if parsed.scheme not in {"http", "https"} or parsed.netloc.lower() != "github.com":
        raise ValueError("project URL must be a github.com URL")

    parts = [part for part in parsed.path.split("/") if part]

    if len(parts) not in {4, 6}:
        raise ValueError(
            "expected a URL like https://github.com/orgs/OWNER/projects/NUMBER "
            "or https://github.com/orgs/OWNER/projects/NUMBER/views/VIEW_NUMBER"
        )

    scope, owner, projects_literal, number_text = parts[:4]

    if scope not in {"orgs", "users"} or projects_literal != "projects":
        raise ValueError("project URL must contain /orgs/OWNER/projects/NUMBER or /users/OWNER/projects/NUMBER")

    try:
        number = int(number_text)
    except ValueError as exc:
        raise ValueError("project number must be an integer") from exc

    view_number = None
    if len(parts) == 6:
        views_literal, view_text = parts[4:]
        if views_literal != "views":
            raise ValueError("unexpected URL suffix; expected /views/VIEW_NUMBER")
        try:
            view_number = int(view_text)
        except ValueError as exc:
            raise ValueError("view number must be an integer") from exc

    return ProjectURL(scope=scope, owner=owner, number=number, view_number=view_number)


def get_project(client: GitHubClient, project_url: ProjectURL) -> dict[str, Any]:
    data = client.graphql(
        PROJECT_QUERY,
        {
            "owner": project_url.owner,
            "number": project_url.number,
            "isOrg": project_url.scope == "orgs",
        },
    )

    container = data.get("organization") if project_url.scope == "orgs" else data.get("user")
    if not container or not container.get("projectV2"):
        raise GitHubAPIError("project not found, or token lacks permission to read it")

    return container["projectV2"]


def choose_board_view(project: dict[str, Any], requested_view_number: int | None) -> dict[str, Any] | None:
    views = safe_nodes(project.get("views"))

    if requested_view_number is not None:
        for view in views:
            if view.get("number") == requested_view_number:
                return view
        raise GitHubAPIError(f"view number {requested_view_number} was not found in this project")

    for view in views:
        layout = str(view.get("layout") or "")
        if "BOARD" in layout.upper():
            return view

    return views[0] if views else None


def infer_column_field_name(project: dict[str, Any], view: dict[str, Any] | None) -> str:
    if view:
        for connection_name in ("groupByFields", "verticalGroupByFields"):
            for field in safe_nodes(view.get(connection_name)):
                name = field.get("name")
                if name:
                    return str(name)

    for field in safe_nodes(project.get("fields")):
        if field.get("name") == "Status":
            return "Status"

    for field in safe_nodes(project.get("fields")):
        data_type = str(field.get("dataType") or "").upper()
        if data_type in {"SINGLE_SELECT", "ITERATION"} and field.get("name"):
            return str(field["name"])

    return "Status"


def ordered_column_names(project: dict[str, Any], column_field_name: str) -> list[str]:
    for field in safe_nodes(project.get("fields")):
        if field.get("name") != column_field_name:
            continue

        if field.get("__typename") == "ProjectV2SingleSelectField":
            return [option["name"] for option in field.get("options", []) if option.get("name")]

        if field.get("__typename") == "ProjectV2IterationField":
            configuration = field.get("configuration") or {}
            return [iteration["title"] for iteration in configuration.get("iterations", []) if iteration.get("title")]

    return []


def safe_nodes(connection: Any) -> list[dict[str, Any]]:
    if isinstance(connection, dict) and isinstance(connection.get("nodes"), list):
        return [node for node in connection["nodes"] if isinstance(node, dict)]
    return []


def iter_project_items(
    client: GitHubClient,
    project_id: str,
    column_field_name: str,
    archived_states: Iterable[str],
) -> Iterator[dict[str, Any]]:
    cursor = None

    while True:
        data = client.graphql(
            ITEMS_QUERY,
            {
                "projectId": project_id,
                "cursor": cursor,
                "columnFieldName": column_field_name,
                "archivedStates": list(archived_states),
            },
        )

        node = data.get("node")
        if not isinstance(node, dict) or "items" not in node:
            raise GitHubAPIError("could not read project items")

        items_connection = node["items"]
        for item in safe_nodes(items_connection):
            yield item

        page_info = items_connection.get("pageInfo") or {}
        if not page_info.get("hasNextPage"):
            break
        cursor = page_info.get("endCursor")


def column_name_for_item(item: dict[str, Any], column_field_name: str) -> str:
    value = item.get("columnValue")
    if not isinstance(value, dict):
        return f"No {column_field_name}"

    typename = value.get("__typename")
    if typename == "ProjectV2ItemFieldSingleSelectValue":
        return str(value.get("name") or f"No {column_field_name}")
    if typename == "ProjectV2ItemFieldIterationValue":
        return str(value.get("title") or f"No {column_field_name}")
    if typename == "ProjectV2ItemFieldTextValue":
        return str(value.get("text") or f"No {column_field_name}")
    if typename == "ProjectV2ItemFieldNumberValue":
        number = value.get("number")
        return str(number) if number is not None else f"No {column_field_name}"
    if typename == "ProjectV2ItemFieldDateValue":
        return str(value.get("date") or f"No {column_field_name}")

    return f"No {column_field_name}"


def iter_issue_timeline_events(
    client: GitHubClient,
    owner: str,
    repo: str,
    issue_number: int,
) -> Iterator[dict[str, Any]]:
    """Yield REST timeline events for an issue or pull request."""
    owner_q = quote(owner, safe="")
    repo_q = quote(repo, safe="")
    path = f"/repos/{owner_q}/{repo_q}/issues/{issue_number}/timeline"
    yield from client.rest_get_paginated(path, params={"per_page": 100})


def iter_sub_issues(
    client: GitHubClient,
    owner: str,
    repo: str,
    issue_number: int,
) -> Iterator[dict[str, Any]]:
    """Yield REST issue objects for the direct sub-issues of an issue."""
    owner_q = quote(owner, safe="")
    repo_q = quote(repo, safe="")
    path = f"/repos/{owner_q}/{repo_q}/issues/{issue_number}/sub_issues"
    yield from client.rest_get_paginated(path, params={"per_page": 100})


def repository_from_rest_issue(
    issue: dict[str, Any],
    fallback_owner: str,
    fallback_repo: str,
) -> tuple[str, str]:
    """Return the repository owner/name for a REST issue response."""
    repository = issue.get("repository")
    if isinstance(repository, dict):
        owner_obj = repository.get("owner")
        owner = login_from_obj(owner_obj) if isinstance(owner_obj, dict) else None
        name = repository.get("name")
        if owner and name:
            return str(owner), str(name)

        name_with_owner = repository.get("full_name") or repository.get("nameWithOwner")
        if isinstance(name_with_owner, str) and "/" in name_with_owner:
            owner, name = name_with_owner.split("/", 1)
            if owner and name:
                return owner, name

    repository_url = issue.get("repository_url")
    if repository_url:
        parsed = urlparse(str(repository_url))
        parts = [part for part in parsed.path.split("/") if part]
        if len(parts) >= 3 and parts[0] == "repos":
            return parts[1], parts[2]

    return fallback_owner, fallback_repo


def rest_issue_to_project_content(
    issue: dict[str, Any],
    fallback_owner: str,
    fallback_repo: str,
) -> dict[str, Any]:
    """Convert a REST issue response to the GraphQL-like content shape used by this script."""
    repo_owner, repo_name = repository_from_rest_issue(issue, fallback_owner, fallback_repo)
    author_login = login_from_obj(issue.get("user")) or login_from_obj(issue.get("author"))
    node_id = issue.get("node_id")
    if not node_id and isinstance(issue.get("id"), str):
        node_id = issue.get("id")
    content: dict[str, Any] = {
        "__typename": "PullRequest" if issue.get("pull_request") else "Issue",
        "number": issue.get("number"),
        "title": issue.get("title"),
        "body": issue.get("body") or "",
        "url": issue.get("html_url") or issue.get("url"),
        "state": issue.get("state"),
        "createdAt": issue.get("created_at") or issue.get("createdAt"),
        "updatedAt": issue.get("updated_at") or issue.get("updatedAt"),
        "closedAt": issue.get("closed_at") or issue.get("closedAt"),
        "author": {"login": author_login or "unknown"},
        "repository": {
            "name": repo_name,
            "nameWithOwner": f"{repo_owner}/{repo_name}",
            "owner": {"login": repo_owner},
        },
    }
    if node_id:
        content["id"] = node_id
    return content


def issue_key(issue: dict[str, Any]) -> tuple[str, str, int] | None:
    """Return a stable owner/repository/issue-number identity for a GraphQL-like issue."""
    repository = issue.get("repository") or {}
    owner_obj = repository.get("owner") if isinstance(repository, dict) else None
    repo_owner = login_from_obj(owner_obj) if isinstance(owner_obj, dict) else None
    repo_name = repository.get("name") if isinstance(repository, dict) else None
    issue_number = issue.get("number")

    html_or_api_url = issue.get("html_url") or issue.get("url")
    if (not repo_owner or not repo_name or not issue_number) and html_or_api_url:
        parsed = urlparse(str(html_or_api_url))
        parts = [part for part in parsed.path.split("/") if part]
        if len(parts) >= 4 and parts[2] in {"issues", "pull"}:
            repo_owner = repo_owner or parts[0]
            repo_name = repo_name or parts[1]
            issue_number = issue_number or parts[3]
        elif len(parts) >= 5 and parts[0] == "repos" and parts[3] in {"issues", "pulls"}:
            repo_owner = repo_owner or parts[1]
            repo_name = repo_name or parts[2]
            issue_number = issue_number or parts[4]

    if not repo_owner or not repo_name or not issue_number:
        return None

    try:
        number = int(issue_number)
    except (TypeError, ValueError):
        return None

    return repo_owner.lower(), repo_name.lower(), number


def is_draft_issue(issue: dict[str, Any]) -> bool:
    return issue.get("__typename") == "DraftIssue"


def project_item_creator_login(item: dict[str, Any]) -> str | None:
    return login_from_obj(item.get("creator"))


def issue_display_title(issue: dict[str, Any]) -> str:
    title = heading_text(issue.get("title"))
    if is_draft_issue(issue):
        return f"{title} (Draft)"
    return title


def issue_key_for_item(item: dict[str, Any]) -> tuple[str, str, int] | None:
    content = item.get("content")
    if not isinstance(content, dict):
        return None
    return issue_key(content)


def original_post_as_entry(issue: dict[str, Any]) -> dict[str, Any]:
    """Return the Issue/PR opening body in the same shape as a Markdown timeline entry."""
    login = login_from_obj(issue.get("author")) or login_from_obj(issue.get("creator")) or "unknown"
    return {
        "kind": "comment",
        "login": login,
        "created_at": issue.get("createdAt"),
        "body": issue.get("body") or "",
        "dedupe_key": f"original:{issue.get('id') or issue.get('url') or issue.get('number')}",
    }


def parse_github_datetime(value: str) -> datetime:
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    if parsed.tzinfo is None:
        return parsed.replace(tzinfo=timezone.utc)
    return parsed


def format_github_datetime(value: str, tz: ZoneInfo) -> str:
    return parse_github_datetime(value).astimezone(tz).strftime("%Y-%m-%d %H:%M:%S %Z")


def human_event_date(value: str, tz: ZoneInfo) -> str:
    if not value:
        return "an unknown date"

    try:
        local_time = parse_github_datetime(value).astimezone(tz)
    except ValueError:
        return str(value)

    return f"{local_time.strftime('%b')} {local_time.day}, {local_time.year}"


def heading_text(value: Any) -> str:
    text = " ".join(str(value or "").splitlines()).strip()
    return text or "(untitled)"


def login_from_obj(value: Any) -> str | None:
    if isinstance(value, dict):
        login = value.get("login") or value.get("name")
        return str(login) if login else None
    if value:
        return str(value)
    return None


def nested_name(value: Any) -> str | None:
    if isinstance(value, dict):
        for key in ("name", "title", "login", "body", "html_url", "url"):
            candidate = value.get(key)
            if candidate:
                return str(candidate)
        return None
    if value is not None:
        return str(value)
    return None


def markdown_inline_code(value: Any) -> str:
    text = str(value or "unknown").replace("`", "\\`")
    return f"`{text}`"


def timeline_entry_heading(entry: dict[str, Any], tz: ZoneInfo) -> str:
    login = str(entry.get("login") or "unknown")
    created_at = entry.get("created_at")
    if not created_at:
        created = "unknown time"
    else:
        try:
            created = format_github_datetime(str(created_at), tz)
        except ValueError:
            created = str(created_at)
    return f"### {login} - {created}"


def project_card_field(event: dict[str, Any], field_name: str) -> str | None:
    project_card = event.get("project_card")
    if isinstance(project_card, dict):
        value = project_card.get(field_name)
        if value:
            return str(value)
    return None


def markdown_issue_title_link(
    title: Any,
    issue: dict[str, Any] | None,
    anchor_by_key: dict[tuple[str, str, int], str],
) -> str:
    """Return a Markdown link for an issue title, preferring local anchors."""
    label = markdown_code_link_label(title)
    if isinstance(issue, dict):
        target = issue_reference_target(issue, anchor_by_key)
        if target:
            return f"[{label}]({target})"
    return markdown_inline_code(title)


def event_body_for_rest_event(
    event: dict[str, Any],
    tz: ZoneInfo,
    anchor_by_key: dict[tuple[str, str, int], str] | None = None,
) -> str:
    anchor_by_key = anchor_by_key or {}
    event_type = str(event.get("event") or "event").lower()
    actor = login_from_obj(event.get("actor")) or login_from_obj(event.get("user")) or "unknown"
    date_text = human_event_date(str(event.get("created_at") or ""), tz)

    if event_type == "assigned":
        assignee = login_from_obj(event.get("assignee")) or "unknown"
        if assignee == actor:
            return f"{actor} self-assigned this on {date_text}"
        return f"{actor} assigned this to {assignee} on {date_text}"

    if event_type == "unassigned":
        assignee = login_from_obj(event.get("assignee")) or "unknown"
        if assignee == actor:
            return f"{actor} unassigned themselves from this on {date_text}"
        return f"{actor} unassigned {assignee} from this on {date_text}"

    if event_type == "labeled":
        label = nested_name(event.get("label")) or "unknown"
        return f"{actor} added {markdown_inline_code(label)} on {date_text}"

    if event_type == "unlabeled":
        label = nested_name(event.get("label")) or "unknown"
        return f"{actor} removed {markdown_inline_code(label)} on {date_text}"

    if event_type == "milestoned":
        milestone = nested_name(event.get("milestone")) or "unknown"
        return f"{actor} added this to the {markdown_inline_code(milestone)} milestone on {date_text}"

    if event_type == "demilestoned":
        milestone = nested_name(event.get("milestone")) or "unknown"
        return f"{actor} removed this from the {markdown_inline_code(milestone)} milestone on {date_text}"

    if event_type == "renamed":
        rename = event.get("rename") or {}
        old_title = rename.get("from") if isinstance(rename, dict) else None
        new_title = rename.get("to") if isinstance(rename, dict) else None
        if old_title and new_title:
            return f"{actor} renamed this from {markdown_inline_code(old_title)} to {markdown_inline_code(new_title)} on {date_text}"
        return f"{actor} renamed this on {date_text}"

    if event_type == "closed":
        return f"{actor} closed this on {date_text}"

    if event_type == "reopened":
        return f"{actor} reopened this on {date_text}"

    if event_type == "locked":
        reason = event.get("lock_reason")
        if reason:
            return f"{actor} locked this as {markdown_inline_code(reason)} on {date_text}"
        return f"{actor} locked this on {date_text}"

    if event_type == "unlocked":
        return f"{actor} unlocked this on {date_text}"

    if event_type == "merged":
        return f"{actor} merged this on {date_text}"

    if event_type == "referenced":
        commit_id = event.get("commit_id")
        if commit_id:
            return f"{actor} referenced this from commit {markdown_inline_code(str(commit_id)[:12])} on {date_text}"
        return f"{actor} referenced this on {date_text}"

    if event_type == "cross-referenced":
        source = event.get("source") or {}
        issue = source.get("issue") if isinstance(source, dict) else None
        title = nested_name(issue) if issue else None
        if title:
            linked_title = markdown_issue_title_link(title, issue, anchor_by_key)
            return f"{actor} cross-referenced this from {linked_title} on {date_text}"
        return f"{actor} cross-referenced this on {date_text}"

    if event_type == "review_requested":
        requested_reviewer = login_from_obj(event.get("requested_reviewer")) or nested_name(event.get("requested_team")) or "unknown"
        return f"{actor} requested a review from {requested_reviewer} on {date_text}"

    if event_type == "review_request_removed":
        requested_reviewer = login_from_obj(event.get("requested_reviewer")) or nested_name(event.get("requested_team")) or "unknown"
        return f"{actor} removed the review request for {requested_reviewer} on {date_text}"

    if event_type == "added_to_project":
        project_name = project_card_field(event, "project_name") or project_card_field(event, "project_url") or "a project"
        column_name = project_card_field(event, "column_name")
        if column_name:
            return f"{actor} added this to {project_name} in {markdown_inline_code(column_name)} on {date_text}"
        return f"{actor} added this to {project_name} on {date_text}"

    if event_type == "moved_columns_in_project":
        project_name = project_card_field(event, "project_name") or project_card_field(event, "project_url") or "a project"
        previous_column = project_card_field(event, "previous_column_name")
        column_name = project_card_field(event, "column_name")
        if previous_column and column_name:
            return f"{actor} moved this in {project_name} from {markdown_inline_code(previous_column)} to {markdown_inline_code(column_name)} on {date_text}"
        if column_name:
            return f"{actor} moved this in {project_name} to {markdown_inline_code(column_name)} on {date_text}"
        return f"{actor} moved this in {project_name} on {date_text}"

    if event_type == "removed_from_project":
        project_name = project_card_field(event, "project_name") or project_card_field(event, "project_url") or "a project"
        return f"{actor} removed this from {project_name} on {date_text}"

    if event_type == "converted_note_to_issue":
        return f"{actor} converted this note to an issue on {date_text}"

    if event_type == "comment_deleted":
        return f"{actor} deleted a comment on {date_text}"

    if event_type in {"pinned", "unpinned", "subscribed", "unsubscribed", "mentioned", "transferred"}:
        action = event_type.replace("_", " ").replace("-", " ")
        return f"{actor} {action} this on {date_text}"

    action = event_type.replace("_", " ").replace("-", " ")
    return f"{actor} {action} this on {date_text}"


def rest_timeline_event_as_entry(
    event: dict[str, Any],
    tz: ZoneInfo,
    anchor_by_key: dict[tuple[str, str, int], str] | None = None,
) -> dict[str, Any]:
    event_type = str(event.get("event") or "event").lower()
    is_comment = event_type == "commented"
    login = login_from_obj(event.get("user")) or login_from_obj(event.get("actor")) or "unknown"
    created_at = event.get("created_at") or event.get("submitted_at") or event.get("createdAt")
    identifier = event.get("node_id") or event.get("id") or event.get("url") or f"{event_type}:{login}:{created_at}"

    return {
        "kind": "comment" if is_comment else "event",
        "login": login,
        "created_at": created_at,
        "body": event.get("body") or "" if is_comment else event_body_for_rest_event(event, tz, anchor_by_key),
        "dedupe_key": f"rest:{identifier}",
    }


def iter_project_v2_timeline_events(client: GitHubClient, content_id: str) -> Iterator[dict[str, Any]]:
    cursor = None
    expected_types = {
        "AddedToProjectV2Event",
        "ProjectV2ItemStatusChangedEvent",
        "RemovedFromProjectV2Event",
        "ConvertedFromDraftEvent",
    }

    while True:
        data = client.graphql(
            PROJECT_V2_TIMELINE_QUERY,
            {
                "contentId": content_id,
                "cursor": cursor,
            },
        )

        node = data.get("node")
        if not isinstance(node, dict):
            return

        timeline_items = node.get("timelineItems")
        if not isinstance(timeline_items, dict):
            return

        for event in safe_nodes(timeline_items):
            if event.get("__typename") in expected_types:
                yield event

        page_info = timeline_items.get("pageInfo") or {}
        if not page_info.get("hasNextPage"):
            break
        cursor = page_info.get("endCursor")


def project_title_from_event(event: dict[str, Any]) -> str:
    project = event.get("project")
    if isinstance(project, dict):
        return str(project.get("title") or project.get("url") or "Project")
    return "Project"


def body_for_project_v2_event(event: dict[str, Any], tz: ZoneInfo) -> str:
    typename = str(event.get("__typename") or "ProjectV2Event")
    actor = login_from_obj(event.get("actor")) or "unknown"
    date_text = human_event_date(str(event.get("createdAt") or ""), tz)
    project_title = project_title_from_event(event)

    if typename == "AddedToProjectV2Event":
        return f"{actor} added this to {project_title} on {date_text}"

    if typename == "ProjectV2ItemStatusChangedEvent":
        previous_status = event.get("previousStatus")
        status = event.get("status")
        if previous_status and status:
            return f"{actor} moved this in {project_title} from {markdown_inline_code(previous_status)} to {markdown_inline_code(status)} on {date_text}"
        if status:
            return f"{actor} set this in {project_title} to {markdown_inline_code(status)} on {date_text}"
        return f"{actor} changed this item's status in {project_title} on {date_text}"

    if typename == "RemovedFromProjectV2Event":
        return f"{actor} removed this from {project_title} on {date_text}"

    if typename == "ConvertedFromDraftEvent":
        return f"{actor} converted this from a draft issue in {project_title} on {date_text}"

    return f"{actor} updated this in {project_title} on {date_text}"


def project_v2_event_as_entry(event: dict[str, Any], tz: ZoneInfo) -> dict[str, Any]:
    typename = str(event.get("__typename") or "ProjectV2Event")
    identifier = event.get("id") or f"{typename}:{event.get('createdAt')}:{project_title_from_event(event)}"
    return {
        "kind": "event",
        "login": login_from_obj(event.get("actor")) or "unknown",
        "created_at": event.get("createdAt"),
        "body": body_for_project_v2_event(event, tz),
        "dedupe_key": f"graphql:{identifier}",
    }


def timeline_sort_value(entry: dict[str, Any]) -> datetime:
    created_at = entry.get("created_at")
    if created_at:
        try:
            return parse_github_datetime(str(created_at))
        except ValueError:
            pass
    return datetime.max.replace(tzinfo=timezone.utc)


def should_omit_timeline_entry(entry: dict[str, Any]) -> bool:
    """Return True for noisy technical timeline events that should not be exported."""
    if entry.get("kind") != "event":
        return False
    body = str(entry.get("body") or "")
    return "project v2" in body.casefold()


def collect_issue_timeline_entries(
    client: GitHubClient,
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    issue: dict[str, Any],
    tz: ZoneInfo,
    anchor_by_key: dict[tuple[str, str, int], str] | None = None,
) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    seen: set[str] = set()

    def add_entry(entry: dict[str, Any]) -> None:
        if should_omit_timeline_entry(entry):
            return

        key = str(entry.get("dedupe_key") or f"{entry.get('kind')}:{entry.get('login')}:{entry.get('created_at')}:{entry.get('body')}")
        if key in seen:
            return
        entry["_order"] = len(entries)
        seen.add(key)
        entries.append(entry)

    add_entry(original_post_as_entry(issue))

    for event in iter_issue_timeline_events(client, repo_owner, repo_name, issue_number):
        if isinstance(event, dict):
            add_entry(rest_timeline_event_as_entry(event, tz, anchor_by_key))

    content_id = issue.get("id")
    if isinstance(content_id, str) and content_id:
        for event in iter_project_v2_timeline_events(client, str(content_id)):
            add_entry(project_v2_event_as_entry(event, tz))

    entries.sort(key=lambda entry: (timeline_sort_value(entry), int(entry.get("_order", 0))))
    return entries


def collect_draft_timeline_entries(item: dict[str, Any], draft_issue: dict[str, Any]) -> list[dict[str, Any]]:
    """Return the exportable body entry for a Project v2 draft issue card."""
    entry = original_post_as_entry(draft_issue)

    if entry.get("login") == "unknown":
        creator_login = project_item_creator_login(item)
        if creator_login:
            entry["login"] = creator_login

    if not entry.get("created_at"):
        entry["created_at"] = item.get("createdAt")

    return [entry]


def ensure_archived_section_at_end(grouped: OrderedDict[str, list[dict[str, Any]]]) -> None:
    """Ensure the synthetic archive section exists and is the final section.

    This uses an internal key instead of the visible heading text so a real
    project column named "Archived" is not merged with the synthetic archive
    section.
    """
    archived_items = grouped.pop(ARCHIVED_SECTION_KEY, [])
    grouped[ARCHIVED_SECTION_KEY] = archived_items


def markdown_section_heading(column_key: str) -> str:
    if column_key == ARCHIVED_SECTION_KEY:
        return ARCHIVED_COLUMN_NAME
    return column_key


def markdown_link_text(value: Any) -> str:
    """Escape text for use inside a Markdown inline-link label."""
    text = str(value or "")
    return text.replace("\\", "\\\\").replace("[", "\\[").replace("]", "\\]")


def markdown_code_link_label(value: Any) -> str:
    """Return inline-code text suitable for use as a Markdown link label."""
    return markdown_inline_code(markdown_link_text(value))


def markdown_heading_plain_text(value: str) -> str:
    """Return approximate rendered text for a Markdown heading.

    This is used only to build GitHub-style heading anchors. It strips common
    inline Markdown forms whose visible text is what GitHub uses for the slug.
    """
    text = str(value or "")
    text = re.sub(r"!\[([^\]]*)\]\([^)]*\)", r"\1", text)
    text = re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", text)
    text = re.sub(r"`([^`]*)`", r"\1", text)
    text = re.sub(r"<[^>]+>", "", text)
    return text


def github_heading_slug(value: str) -> str:
    """Return a GitHub-style slug for a Markdown heading."""
    text = markdown_heading_plain_text(value).strip().lower()
    text = re.sub(r"[^\w\s-]", "", text, flags=re.UNICODE)
    text = re.sub(r"\s+", "-", text)
    return text.strip("-")


class HeadingAnchorTracker:
    """Track duplicate GitHub-style heading anchors in render order."""

    def __init__(self) -> None:
        self._seen: dict[str, int] = {}

    def anchor_for(self, heading: str) -> str:
        slug = github_heading_slug(heading)
        count = self._seen.get(slug, 0)
        self._seen[slug] = count + 1
        if count:
            return f"{slug}-{count}"
        return slug


def archived_issue_heading(
    issue: dict[str, Any],
    item: dict[str, Any],
    parent_anchor_by_key: dict[tuple[str, str, int], str] | None = None,
    parent_anchor_by_title: dict[str, str] | None = None,
    parent_label_by_key: dict[tuple[str, str, int], str] | None = None,
) -> str:
    archived_from = item.get(ARCHIVED_FROM_COLUMN_KEY) or "unknown column"
    return (
        f"{issue_base_heading(issue, item, parent_anchor_by_key, parent_anchor_by_title, parent_label_by_key)} "
        f'(archived from "{heading_text(archived_from)}")'
    )


def issue_reference_label(issue: dict[str, Any]) -> str | None:
    """Return the visible owner/repository issue reference used in issue headings."""
    details = issue_repository_details(issue)
    if not details:
        return None

    repo_owner, repo_name, issue_number = details
    return f"{repo_owner}/{repo_name} #{issue_number}"


def issue_heading_link(issue: dict[str, Any]) -> str | None:
    """Return the absolute GitHub issue/PR link used at the start of a heading."""
    label = issue_reference_label(issue)
    url = issue_url(issue)
    if not label or not url:
        return None
    return f"[{markdown_code_link_label(label)}]({url})"


def sub_issue_parent_reference(
    item: dict[str, Any],
    parent_anchor_by_key: dict[tuple[str, str, int], str] | None = None,
    parent_anchor_by_title: dict[str, str] | None = None,
    parent_label_by_key: dict[tuple[str, str, int], str] | None = None,
) -> str | None:
    parent_title = item.get(SUB_ISSUE_PARENT_TITLE_KEY)
    if not parent_title:
        return None

    parent_text = heading_text(parent_title)
    parent_anchor = None
    parent_label = None
    parent_key = item.get(SUB_ISSUE_PARENT_KEY_KEY)
    if parent_label_by_key and isinstance(parent_key, tuple):
        parent_label = parent_label_by_key.get(parent_key)
    if parent_anchor_by_key and isinstance(parent_key, tuple):
        parent_anchor = parent_anchor_by_key.get(parent_key)
    if not parent_anchor and parent_anchor_by_title:
        parent_anchor = parent_anchor_by_title.get(parent_text)

    label = parent_label or parent_text

    if not parent_anchor:
        if parent_label:
            return markdown_inline_code(label)
        return label

    if parent_label:
        return f"[{markdown_code_link_label(label)}](#{parent_anchor})"
    return f"[{markdown_link_text(label)}](#{parent_anchor})"


def issue_base_heading(
    issue: dict[str, Any],
    item: dict[str, Any],
    parent_anchor_by_key: dict[tuple[str, str, int], str] | None = None,
    parent_anchor_by_title: dict[str, str] | None = None,
    parent_label_by_key: dict[tuple[str, str, int], str] | None = None,
) -> str:
    title = issue_display_title(issue)
    prefix = issue_heading_link(issue)
    if prefix:
        title = f"{prefix}: {title}"

    parent_reference = sub_issue_parent_reference(
        item,
        parent_anchor_by_key,
        parent_anchor_by_title,
        parent_label_by_key,
    )
    if parent_reference:
        title = f"{title} (sub-issue of {parent_reference})"
    return title


def issue_heading(
    issue: dict[str, Any],
    item: dict[str, Any],
    column: str,
    parent_anchor_by_key: dict[tuple[str, str, int], str] | None = None,
    parent_anchor_by_title: dict[str, str] | None = None,
    parent_label_by_key: dict[tuple[str, str, int], str] | None = None,
) -> str:
    if column == ARCHIVED_SECTION_KEY:
        return archived_issue_heading(
            issue,
            item,
            parent_anchor_by_key,
            parent_anchor_by_title,
            parent_label_by_key,
        )
    return issue_base_heading(issue, item, parent_anchor_by_key, parent_anchor_by_title, parent_label_by_key)


def compute_issue_heading_anchors(
    grouped: OrderedDict[str, list[dict[str, Any]]],
) -> tuple[dict[tuple[str, str, int], str], dict[str, str], dict[tuple[str, str, int], str]]:
    """Precompute anchors for generated issue headings.

    GitHub de-duplicates heading anchors by render order. Including the top-level
    column headings here keeps links correct when a column and an issue share the
    same heading text. Timeline-entry headings are not known until issue histories
    are fetched, but they are extremely unlikely to collide with issue titles.
    """
    tracker = HeadingAnchorTracker()
    anchor_by_key: dict[tuple[str, str, int], str] = {}
    anchor_by_title: dict[str, str] = {}
    label_by_key: dict[tuple[str, str, int], str] = {}

    for items in grouped.values():
        for item in items:
            issue = item.get("content")
            if not isinstance(issue, dict):
                continue

            key = issue_key(issue)
            label = issue_reference_label(issue)
            if key and label:
                label_by_key.setdefault(key, label)

    for column, items in grouped.items():
        tracker.anchor_for(heading_text(markdown_section_heading(column)))

        for item in items:
            issue = item.get("content")
            if not isinstance(issue, dict):
                continue

            heading = issue_heading(issue, item, column, parent_label_by_key=label_by_key)
            anchor = tracker.anchor_for(heading)

            key = issue_key(issue)
            if key and key not in anchor_by_key:
                anchor_by_key[key] = anchor

            raw_title = heading_text(issue.get("title"))
            anchor_by_title.setdefault(raw_title, anchor)
            anchor_by_title.setdefault(issue_display_title(issue), anchor)

    return anchor_by_key, anchor_by_title, label_by_key


def issue_url(issue: dict[str, Any]) -> str | None:
    html_url = issue.get("html_url")
    if html_url:
        return str(html_url)

    url = issue.get("url")
    if not url:
        return None

    parsed = urlparse(str(url))
    parts = [part for part in parsed.path.split("/") if part]
    if len(parts) >= 5 and parts[0] == "repos" and parts[3] in {"issues", "pulls"}:
        try:
            number = int(parts[4])
        except ValueError:
            return str(url)
        path_kind = "pull" if parts[3] == "pulls" else "issues"
        owner_q = quote(parts[1], safe="")
        repo_q = quote(parts[2], safe="")
        return f"https://github.com/{owner_q}/{repo_q}/{path_kind}/{number}"

    return str(url)


def github_issue_url(repo_owner: str, repo_name: str, issue_number: int | str) -> str:
    """Return a stable GitHub web URL for an issue-style reference."""
    owner_q = quote(str(repo_owner), safe="")
    repo_q = quote(str(repo_name), safe="")
    return f"https://github.com/{owner_q}/{repo_q}/issues/{int(issue_number)}"


def issue_reference_target(
    issue: dict[str, Any],
    anchor_by_key: dict[tuple[str, str, int], str],
) -> str | None:
    """Return a local heading target for exported issues, otherwise the GitHub URL."""
    key = issue_key(issue)
    if key:
        anchor = anchor_by_key.get(key)
        if anchor:
            return f"#{anchor}"

    url = issue_url(issue)
    if url:
        return url

    details = issue_repository_details(issue)
    if details:
        repo_owner, repo_name, issue_number = details
        return github_issue_url(repo_owner, repo_name, issue_number)

    return None

def issue_repository_details(issue: dict[str, Any]) -> tuple[str, str, int] | None:
    repository = issue.get("repository") or {}
    repo_owner = None
    repo_name = None
    issue_number = issue.get("number")

    if isinstance(repository, dict):
        owner_obj = repository.get("owner") or {}
        repo_owner = login_from_obj(owner_obj)
        repo_name = repository.get("name")

    html_or_api_url = issue.get("html_url") or issue.get("url")
    if (not repo_owner or not repo_name or issue_number is None) and html_or_api_url:
        parsed = urlparse(str(html_or_api_url))
        parts = [part for part in parsed.path.split("/") if part]
        if len(parts) >= 4 and parts[2] in {"issues", "pull"}:
            repo_owner = repo_owner or parts[0]
            repo_name = repo_name or parts[1]
            issue_number = issue_number if issue_number is not None else parts[3]
        elif len(parts) >= 5 and parts[0] == "repos" and parts[3] in {"issues", "pulls"}:
            repo_owner = repo_owner or parts[1]
            repo_name = repo_name or parts[2]
            issue_number = issue_number if issue_number is not None else parts[4]

    if not repo_owner or not repo_name or issue_number is None:
        return None

    try:
        number = int(issue_number)
    except (TypeError, ValueError):
        return None

    return str(repo_owner), str(repo_name), number


def merge_ranges(ranges: list[tuple[int, int]], text_length: int) -> list[tuple[int, int]]:
    """Return sorted, non-overlapping protected Markdown character ranges."""
    normalized = sorted(
        (max(0, start), min(text_length, end))
        for start, end in ranges
        if end > start
    )
    merged: list[tuple[int, int]] = []
    for start, end in normalized:
        if not merged or start > merged[-1][1]:
            merged.append((start, end))
        else:
            merged[-1] = (merged[-1][0], max(merged[-1][1], end))
    return merged


def fenced_code_block_ranges(markdown: str) -> list[tuple[int, int]]:
    """Return character ranges for fenced code blocks in Markdown."""
    ranges: list[tuple[int, int]] = []
    in_fence = False
    fence_char = ""
    fence_length = 0
    fence_start = 0
    offset = 0

    for line in markdown.splitlines(keepends=True):
        if not in_fence:
            match = re.match(r" {0,3}(`{3,}|~{3,})", line)
            if match:
                marker = match.group(1)
                in_fence = True
                fence_char = marker[0]
                fence_length = len(marker)
                fence_start = offset
        else:
            match = re.match(rf" {{0,3}}({re.escape(fence_char)}{{{fence_length},}})\s*$", line)
            if match:
                ranges.append((fence_start, offset + len(line)))
                in_fence = False

        offset += len(line)

    if in_fence:
        ranges.append((fence_start, len(markdown)))

    return ranges


def markdown_link_protected_ranges(markdown: str) -> list[tuple[int, int]]:
    """Return ranges where issue-reference autolinking should not be applied."""
    ranges = fenced_code_block_ranges(markdown)

    protected_patterns = [
        r"(?s)(`+)(?:(?!\1).)*\1",  # inline code spans
        r"!?\[[^\]\n]*\]\([^\)\n]*\)",  # inline links and images
        r"!?\[[^\]\n]*\]\[[^\]\n]*\]",  # reference-style links and images
        r"(?m)^ {0,3}\[[^\]\n]+\]:\s+\S.*$",  # reference-link definitions
        r"https?://[^\s<>)\]]+",  # raw URLs
        r"<[^>\s]+>",  # autolinks and simple HTML tags
    ]
    for pattern in protected_patterns:
        for match in re.finditer(pattern, markdown):
            ranges.append(match.span())

    return merge_ranges(ranges, len(markdown))


def replace_issue_references_in_segment(
    segment: str,
    repo_owner: str | None,
    repo_name: str | None,
    anchor_by_key: dict[tuple[str, str, int], str],
) -> str:
    """Replace GitHub issue references in an unprotected Markdown segment.

    Prefer local anchors for issues exported into this Markdown file. If a
    referenced issue is not exported, link to the issue's GitHub URL instead of
    creating or leaving a dead local reference.
    """
    reference_pattern = re.compile(
        r"(?<![\w./-])"
        r"(?:(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+))?"
        r"#(?P<number>[1-9][0-9]*)\b"
    )

    def replacement(match: re.Match[str]) -> str:
        number_text = match.group("number")
        owner = match.group("owner") or repo_owner
        repo = match.group("repo") or repo_name
        if not owner or not repo:
            return match.group(0)

        number = int(number_text)
        key = (owner.lower(), repo.lower(), number)
        anchor = anchor_by_key.get(key)
        target = f"#{anchor}" if anchor else github_issue_url(owner, repo, number)
        return f"[{markdown_link_text(match.group(0))}]({target})"

    return reference_pattern.sub(replacement, segment)


def link_issue_references(
    markdown: str,
    current_issue: dict[str, Any],
    anchor_by_key: dict[tuple[str, str, int], str],
) -> str:
    """Link issue references to exported headings or GitHub as a safe fallback."""
    if not markdown:
        return markdown

    repo_owner = None
    repo_name = None
    details = issue_repository_details(current_issue)
    if details:
        repo_owner, repo_name, _issue_number = details

    ranges = markdown_link_protected_ranges(markdown)
    if not ranges:
        return replace_issue_references_in_segment(markdown, repo_owner, repo_name, anchor_by_key)

    pieces: list[str] = []
    cursor = 0
    for start, end in ranges:
        if cursor < start:
            pieces.append(
                replace_issue_references_in_segment(markdown[cursor:start], repo_owner, repo_name, anchor_by_key)
            )
        pieces.append(markdown[start:end])
        cursor = end

    if cursor < len(markdown):
        pieces.append(replace_issue_references_in_segment(markdown[cursor:], repo_owner, repo_name, anchor_by_key))

    return "".join(pieces)


def issue_can_have_sub_issues(issue: dict[str, Any]) -> bool:
    return issue.get("__typename") == "Issue" and issue_repository_details(issue) is not None


def project_item_issue_keys(grouped: OrderedDict[str, list[dict[str, Any]]]) -> set[tuple[str, str, int]]:
    keys: set[tuple[str, str, int]] = set()
    for items in grouped.values():
        for item in items:
            key = issue_key_for_item(item)
            if key:
                keys.add(key)
    return keys


def synthetic_sub_issue_item(
    sub_issue: dict[str, Any],
    parent_item: dict[str, Any],
    parent_title: str,
    parent_key: tuple[str, str, int] | None,
) -> dict[str, Any]:
    item: dict[str, Any] = {
        "id": f"sub_issue:{sub_issue.get('id') or sub_issue.get('url') or sub_issue.get('number')}",
        "type": "ISSUE",
        "isArchived": bool(parent_item.get("isArchived")),
        "content": sub_issue,
        SUB_ISSUE_PARENT_TITLE_KEY: parent_title,
    }

    if parent_key:
        item[SUB_ISSUE_PARENT_KEY_KEY] = parent_key

    if ARCHIVED_FROM_COLUMN_KEY in parent_item:
        item[ARCHIVED_FROM_COLUMN_KEY] = parent_item[ARCHIVED_FROM_COLUMN_KEY]

    return item


def add_sub_issues_to_grouped_items(
    client: GitHubClient,
    grouped: OrderedDict[str, list[dict[str, Any]]],
) -> OrderedDict[str, list[dict[str, Any]]]:
    """Insert missing sub-issues after their parent item and annotate known sub-issue cards.

    If a sub-issue is already present as a Project item, it stays in its normal Project
    column/order and only receives the parent-title heading suffix. Sub-issues that are
    not Project items are inserted directly after their parent, in the parent's section.
    """
    project_keys = project_item_issue_keys(grouped)
    synthetic_keys: set[tuple[str, str, int]] = set()
    parent_title_by_key: dict[tuple[str, str, int], str] = {}
    parent_key_by_key: dict[tuple[str, str, int], tuple[str, str, int]] = {}
    sub_issue_cache: dict[tuple[str, str, int], list[dict[str, Any]]] = {}

    def direct_sub_issue_contents(issue: dict[str, Any]) -> list[dict[str, Any]]:
        if not issue_can_have_sub_issues(issue):
            return []

        key = issue_key(issue)
        details = issue_repository_details(issue)
        if not key or not details:
            return []

        if key in sub_issue_cache:
            return sub_issue_cache[key]

        repo_owner, repo_name, issue_number = details
        sub_issues: list[dict[str, Any]] = []
        for sub_issue in iter_sub_issues(client, repo_owner, repo_name, issue_number):
            if isinstance(sub_issue, dict):
                sub_issues.append(rest_issue_to_project_content(sub_issue, repo_owner, repo_name))

        sub_issue_cache[key] = sub_issues
        return sub_issues

    def expand_item(item: dict[str, Any], ancestors: set[tuple[str, str, int]]) -> list[dict[str, Any]]:
        content = item.get("content")
        if not isinstance(content, dict):
            return [item]

        parent_key = issue_key(content)
        if parent_key and parent_key in ancestors:
            return [item]

        next_ancestors = set(ancestors)
        if parent_key:
            next_ancestors.add(parent_key)

        expanded = [item]
        parent_title = heading_text(content.get("title"))

        for sub_issue in direct_sub_issue_contents(content):
            sub_key = issue_key(sub_issue)
            if not sub_key or sub_key in next_ancestors:
                continue

            parent_title_by_key.setdefault(sub_key, parent_title)
            if parent_key:
                parent_key_by_key.setdefault(sub_key, parent_key)

            if sub_key in project_keys or sub_key in synthetic_keys:
                continue

            synthetic_keys.add(sub_key)
            sub_item = synthetic_sub_issue_item(sub_issue, item, parent_title, parent_key)
            expanded.extend(expand_item(sub_item, next_ancestors))

        return expanded

    expanded_grouped: OrderedDict[str, list[dict[str, Any]]] = OrderedDict()
    for column, items in grouped.items():
        expanded_items: list[dict[str, Any]] = []
        for item in tqdm(items, desc=column):
            expanded_items.extend(expand_item(item, set()))
        expanded_grouped[column] = expanded_items

    for items in tqdm(expanded_grouped.values(), desc="Expanded"):
        for item in items:
            key = issue_key_for_item(item)
            if key and key in parent_title_by_key:
                item.setdefault(SUB_ISSUE_PARENT_TITLE_KEY, parent_title_by_key[key])
                if key in parent_key_by_key:
                    item.setdefault(SUB_ISSUE_PARENT_KEY_KEY, parent_key_by_key[key])

    ensure_archived_section_at_end(expanded_grouped)
    return expanded_grouped


def group_project_items(
    client: GitHubClient,
    project: dict[str, Any],
    column_field_name: str,
) -> tuple[OrderedDict[str, list[dict[str, Any]]], dict[str, int]]:
    columns = ordered_column_names(project, column_field_name)
    grouped: OrderedDict[str, list[dict[str, Any]]] = OrderedDict((column, []) for column in columns)
    ensure_archived_section_at_end(grouped)
    stats = {
        "items_seen": 0,
        "issue_or_pr_items": 0,
        "draft_items_exported": 0,
        "archived_issue_or_pr_items": 0,
        "archived_draft_items": 0,
        "draft_items_skipped": 0,
        "redacted_items_skipped": 0,
        "other_items_skipped": 0,
    }

    def record_item(item: dict[str, Any], *, archived: bool) -> None:
        stats["items_seen"] += 1
        content = item.get("content")
        content_type = content.get("__typename") if isinstance(content, dict) else None

        if content_type not in {"Issue", "PullRequest", "DraftIssue"}:
            if content_type is None or item.get("type") == "REDACTED":
                stats["redacted_items_skipped"] += 1
            else:
                stats["other_items_skipped"] += 1
            return

        if content_type == "DraftIssue":
            stats["draft_items_exported"] += 1
        else:
            stats["issue_or_pr_items"] += 1

        column = column_name_for_item(item, column_field_name)

        if archived:
            if content_type == "DraftIssue":
                stats["archived_draft_items"] += 1
            else:
                stats["archived_issue_or_pr_items"] += 1
            archived_item = dict(item)
            archived_item[ARCHIVED_FROM_COLUMN_KEY] = column
            grouped.setdefault(ARCHIVED_SECTION_KEY, []).append(archived_item)
            ensure_archived_section_at_end(grouped)
            return

        grouped.setdefault(column, []).append(item)

    for item in tqdm(iter_project_items(client, project["id"], column_field_name, ("NOT_ARCHIVED",)), desc="Current"):
        record_item(item, archived=False)

    ensure_archived_section_at_end(grouped)

    for item in tqdm(iter_project_items(client, project["id"], column_field_name, ("ARCHIVED",)), desc="Archived"):
        record_item(item, archived=True)

    ensure_archived_section_at_end(grouped)
    return grouped, stats


def build_markdown(
    client: GitHubClient,
    grouped: OrderedDict[str, list[dict[str, Any]]],
    tz: ZoneInfo,
) -> tuple[str, dict[str, int]]:
    lines: list[str] = []
    entry_count = 0
    comment_count = 0
    timeline_event_count = 0
    sub_issue_count = 0
    parent_anchor_by_key, parent_anchor_by_title, parent_label_by_key = compute_issue_heading_anchors(grouped)

    for column, items in grouped.items():
        lines.append(f"# {heading_text(markdown_section_heading(column))}")
        lines.append("")

        for item in tqdm(items, desc=column):
            issue = item["content"]
            if item.get(SUB_ISSUE_PARENT_TITLE_KEY):
                sub_issue_count += 1
            heading = issue_heading(
                issue,
                item,
                column,
                parent_anchor_by_key,
                parent_anchor_by_title,
                parent_label_by_key,
            )
            lines.append(f"## {heading}")
            lines.append("")

            if is_draft_issue(issue):
                entries = collect_draft_timeline_entries(item, issue)
            else:
                details = issue_repository_details(issue)
                if not details:
                    lines.append("<!-- Skipped timeline: missing repository or issue number in API response. -->")
                    lines.append("")
                    continue

                repo_owner, repo_name, issue_number = details
                entries = collect_issue_timeline_entries(
                    client,
                    str(repo_owner),
                    str(repo_name),
                    int(issue_number),
                    issue,
                    tz,
                    parent_anchor_by_key,
                )

            for entry in entries:
                entry_count += 1
                if entry.get("kind") == "comment":
                    comment_count += 1
                else:
                    timeline_event_count += 1

                lines.append(timeline_entry_heading(entry, tz))
                lines.append("")
                lines.append(link_issue_references(str(entry.get("body") or ""), issue, parent_anchor_by_key))
                lines.append("")

    # End files with exactly one newline.
    return "\n".join(lines).rstrip() + "\n", {
        "entries_exported": entry_count,
        "comments_exported": comment_count,
        "timeline_events_exported": timeline_event_count,
        "sub_issue_items_exported": sub_issue_count,
    }


def export_project(project_url: str, output_path: Path, tz_name: str = DEFAULT_TZ) -> dict[str, int | str]:
    print(f"Exporting project: {project_url}", file=sys.stderr)
    parsed_project_url = parse_project_url(project_url)
    print("Getting GitHub token...", file=sys.stderr)
    token = get_github_token(parsed_project_url)

    print("Getting timezone...", file=sys.stderr)
    try:
        tz = ZoneInfo(tz_name)
    except ZoneInfoNotFoundError as exc:
        raise GitHubAPIError(f"unknown timezone: {tz_name}") from exc

    print("Initializing client...", file=sys.stderr)
    client = GitHubClient(token)

    print("Loading initial project data...", file=sys.stderr)
    project = get_project(client, parsed_project_url)
    view = choose_board_view(project, parsed_project_url.view_number)
    column_field_name = infer_column_field_name(project, view)

    print("Grouping project items...", file=sys.stderr)
    grouped, stats = group_project_items(client, project, column_field_name)

    print("Loading sub-issues...", file=sys.stderr)
    grouped = add_sub_issues_to_grouped_items(client, grouped)

    print("Building Markdown...", file=sys.stderr)
    markdown, markdown_stats = build_markdown(client, grouped, tz)

    print(f"Writing Markdown to file: {output_path}", file=sys.stderr)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(markdown, encoding="utf-8")

    return {
        **stats,
        **markdown_stats,
        "columns_written": len(grouped),
        "project_title": str(project.get("title") or ""),
        "column_field": column_field_name,
        "view_name": str(view.get("name") if view else ""),
    }


def parse_args(argv: Iterable[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Export issue comments and timeline events from a GitHub Projects v2 board to Markdown.",
    )
    parser.add_argument(
        "-p",
        "--project",
        required=True,
        help="GitHub Projects v2 URL, e.g. https://github.com/orgs/veg/projects/32",
    )
    parser.add_argument(
        "-o",
        "--output",
        required=True,
        help="Path to the Markdown file to create.",
    )
    return parser.parse_args(list(argv))


def main(argv: Iterable[str] = sys.argv[1:]) -> int:
    args = parse_args(argv)

    try:
        stats = export_project(args.project, Path(args.output))
    except (GitHubAPIError, ValueError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    print(
        "Exported "
        f"{stats['entries_exported']} Markdown entries "
        f"({stats['comments_exported']} comments/original posts and "
        f"{stats['timeline_events_exported']} timeline events) from "
        f"{stats['issue_or_pr_items']} issue/PR cards, "
        f"{stats['draft_items_exported']} draft cards, "
        f"plus {stats['sub_issue_items_exported']} sub-issues "
        f"({stats['archived_issue_or_pr_items']} archived issue/PR cards and "
        f"{stats['archived_draft_items']} archived draft cards) "
        f"across {stats['columns_written']} columns "
        f"to {args.output}",
        file=sys.stderr,
    )

    skipped = (
        int(stats["redacted_items_skipped"])
        + int(stats["other_items_skipped"])
    )
    if skipped:
        print(
            "Skipped "
            f"{stats['redacted_items_skipped']} redacted and "
            f"{stats['other_items_skipped']} other non-issue/non-PR/non-draft project items.",
            file=sys.stderr,
        )

    return 0

if __name__ == "__main__":
    raise SystemExit(main())
