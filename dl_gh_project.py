#!/usr/bin/env python3
"""
Export the issue-comment history of a GitHub Projects v2 board to Markdown.

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
    - It exports issue comments and pull-request issue comments. It does not
      export pull-request review comments or draft-project-item text.
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
from datetime import datetime
from pathlib import Path
from typing import Any, Iterable, Iterator
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urlencode, urlparse
from urllib.request import Request, urlopen
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError


API_VERSION = "2026-03-10"
GRAPHQL_URL = "https://api.github.com/graphql"
REST_BASE_URL = "https://api.github.com"
DEFAULT_TZ = "UTC"
USER_AGENT = "dl-gh-project/1.1"


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
query($projectId: ID!, $cursor: String, $columnFieldName: String!) {
  node(id: $projectId) {
    ... on ProjectV2 {
      items(
        first: 50,
        after: $cursor,
        archivedStates: [NOT_ARCHIVED],
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
            }
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
        "description": "Export GitHub Project issue comments to Markdown",
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
        "This script needs a token that can read the GitHub Project and the referenced issue / PR comments.\n\n"
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
) -> Iterator[dict[str, Any]]:
    cursor = None

    while True:
        data = client.graphql(
            ITEMS_QUERY,
            {
                "projectId": project_id,
                "cursor": cursor,
                "columnFieldName": column_field_name,
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


def iter_issue_comments(
    client: GitHubClient,
    owner: str,
    repo: str,
    issue_number: int,
) -> Iterator[dict[str, Any]]:
    owner_q = quote(owner, safe="")
    repo_q = quote(repo, safe="")
    path = f"/repos/{owner_q}/{repo_q}/issues/{issue_number}/comments"
    yield from client.rest_get_paginated(path, params={"per_page": 100})


def original_post_as_comment(issue: dict[str, Any]) -> dict[str, Any]:
    """Return the Issue/PR opening body in the same shape as a REST issue comment."""
    author = issue.get("author") or {}
    return {
        "user": {"login": author.get("login") or "unknown"},
        "created_at": issue.get("createdAt"),
        "body": issue.get("body") or "",
    }


def parse_github_datetime(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def format_github_datetime(value: str, tz: ZoneInfo) -> str:
    return parse_github_datetime(value).astimezone(tz).strftime("%Y-%m-%d %H:%M:%S %Z")


def heading_text(value: Any) -> str:
    text = " ".join(str(value or "").splitlines()).strip()
    return text or "(untitled)"


def comment_heading(comment: dict[str, Any], tz: ZoneInfo) -> str:
    user = comment.get("user") or {}
    login = user.get("login") or "unknown"
    created_at = comment.get("created_at")
    if not created_at:
        created = "unknown time"
    else:
        created = format_github_datetime(str(created_at), tz)
    return f"### {login} - {created}"


def group_project_items(
    client: GitHubClient,
    project: dict[str, Any],
    column_field_name: str,
) -> tuple[OrderedDict[str, list[dict[str, Any]]], dict[str, int]]:
    columns = ordered_column_names(project, column_field_name)
    grouped: OrderedDict[str, list[dict[str, Any]]] = OrderedDict((column, []) for column in columns)
    stats = {
        "items_seen": 0,
        "issue_or_pr_items": 0,
        "draft_items_skipped": 0,
        "redacted_items_skipped": 0,
        "other_items_skipped": 0,
    }

    for item in iter_project_items(client, project["id"], column_field_name):
        stats["items_seen"] += 1
        content = item.get("content")
        content_type = content.get("__typename") if isinstance(content, dict) else None

        if content_type not in {"Issue", "PullRequest"}:
            if content_type == "DraftIssue":
                stats["draft_items_skipped"] += 1
            elif content_type is None or item.get("type") == "REDACTED":
                stats["redacted_items_skipped"] += 1
            else:
                stats["other_items_skipped"] += 1
            continue

        stats["issue_or_pr_items"] += 1
        column = column_name_for_item(item, column_field_name)
        grouped.setdefault(column, []).append(item)

    return grouped, stats


def build_markdown(
    client: GitHubClient,
    grouped: OrderedDict[str, list[dict[str, Any]]],
    tz: ZoneInfo,
) -> tuple[str, int]:
    lines: list[str] = []
    comment_count = 0

    for column, items in grouped.items():
        lines.append(f"# {heading_text(column)}")
        lines.append("")

        for item in items:
            issue = item["content"]
            lines.append(f"## {heading_text(issue.get('title'))}")
            lines.append("")

            repository = issue.get("repository") or {}
            owner_obj = repository.get("owner") or {}
            repo_owner = owner_obj.get("login")
            repo_name = repository.get("name")
            issue_number = issue.get("number")

            if not repo_owner or not repo_name or not issue_number:
                lines.append("<!-- Skipped comments: missing repository or issue number in API response. -->")
                lines.append("")
                continue

            original_post = original_post_as_comment(issue)
            comment_count += 1
            lines.append(comment_heading(original_post, tz))
            lines.append("")
            lines.append(original_post.get("body") or "")
            lines.append("")

            for comment in iter_issue_comments(client, str(repo_owner), str(repo_name), int(issue_number)):
                comment_count += 1
                lines.append(comment_heading(comment, tz))
                lines.append("")
                lines.append(comment.get("body") or "")
                lines.append("")

    # End files with exactly one newline.
    return "\n".join(lines).rstrip() + "\n", comment_count


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

    print("Building Markdown...", file=sys.stderr)
    markdown, comment_count = build_markdown(client, grouped, tz)

    print(f"Writing Markdown to file: {markdown}", file=sys.stderr)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(markdown, encoding="utf-8")

    return {
        **stats,
        "comments_exported": comment_count,
        "columns_written": len(grouped),
        "project_title": str(project.get("title") or ""),
        "column_field": column_field_name,
        "view_name": str(view.get("name") if view else ""),
    }


def parse_args(argv: Iterable[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Export all issue comments from a GitHub Projects v2 board to Markdown.",
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
        f"{stats['comments_exported']} comments from "
        f"{stats['issue_or_pr_items']} issue/PR cards "
        f"across {stats['columns_written']} columns "
        f"to {args.output}",
        file=sys.stderr,
    )

    skipped = (
        int(stats["draft_items_skipped"])
        + int(stats["redacted_items_skipped"])
        + int(stats["other_items_skipped"])
    )
    if skipped:
        print(
            "Skipped "
            f"{stats['draft_items_skipped']} draft, "
            f"{stats['redacted_items_skipped']} redacted, and "
            f"{stats['other_items_skipped']} other non-issue/non-PR project items.",
            file=sys.stderr,
        )

    return 0

if __name__ == "__main__":
    raise SystemExit(main())
