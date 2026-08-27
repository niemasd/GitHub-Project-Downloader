#!/usr/bin/env python3
"""
Export the issue, comment, and timeline history of a GitHub Projects v2 board to Markdown.

Usage:
    ./dl_gh_project.py --project PROJECT_URL --output OUTPUT.md
    ./dl_gh_project.py -p PROJECT_URL -o OUTPUT.md [-j WORKERS]
    ./dl_gh_project.py -p PROJECT_URL -o OUTPUT.md --whitelist niemasd veg

Authentication:
    Set GITHUB_TOKEN or GH_TOKEN in the environment. If neither is set, the
    script interactively prompts for a token. For private projects or
    repositories, the token needs permission to read the project and the
    referenced issues / pull requests.

Notes:
    - This script uses the Python standard library plus tqdm for progress bars.
    - It supports modern Projects v2 URLs:
        https://github.com/orgs/OWNER/projects/NUMBER
        https://github.com/users/OWNER/projects/NUMBER
        https://github.com/orgs/OWNER/projects/NUMBER/views/VIEW_NUMBER
    - It exports issue opening posts, issue comments, and issue / pull-request timeline events.
    - It exports draft project items as draft-only sections with their bodies.
    - It also exports issue sub-issues as peer Markdown sections after their parent issue.
    - It recursively exports issues / pull requests referenced by exported content.
    - Use --whitelist ACCOUNT [ACCOUNT ...] to restrict recursive reference
      discovery to repositories owned by those GitHub accounts / organizations.
    - It downloads embedded images next to the Markdown file and rewrites them as local links.
    - Use --workers N to opt into bounded parallel API reads; --workers 1 is serial.
    - It does not export pull-request review comments.
"""

from __future__ import annotations

import argparse
import getpass
import html
import json
import mimetypes
import os
import re
import sys
import threading
import time
import unicodedata
from collections import OrderedDict
from concurrent.futures import Future, ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
from multiprocessing import cpu_count
from pathlib import Path
from typing import Any, Iterable, Iterator
from urllib.error import HTTPError, URLError
from urllib.parse import quote, unquote, urlencode, urljoin, urlparse, urlunparse
from urllib.request import HTTPRedirectHandler, Request, build_opener, urlopen
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

from tqdm import tqdm

API_VERSION = "2026-03-10"
GRAPHQL_URL = "https://api.github.com/graphql"
REST_BASE_URL = "https://api.github.com"
DEFAULT_TZ = "UTC"
DEFAULT_WORKERS = cpu_count()
MAX_WORKERS = 16
CONCURRENT_REQUEST_SPACING_SECONDS = 0.10
MAX_API_RETRIES = 5
USER_AGENT = "dl-gh-project-v2/1.9"
ARCHIVED_COLUMN_NAME = "Archived"
ARCHIVED_SECTION_KEY = "__dl_gh_project_archived_items__"
ARCHIVED_FROM_COLUMN_KEY = "_dl_gh_project_archived_from_column"
REFERENCED_COLUMN_NAME = "Referenced issues"
REFERENCED_SECTION_KEY = "__dl_gh_project_referenced_items__"
REFERENCED_ITEM_KEY = "_dl_gh_project_referenced_item"
REFERENCE_SCAN_COMPLETE_KEY = "_dl_gh_project_reference_scan_complete"
TIMELINE_ENTRIES_KEY = "_dl_gh_project_timeline_entries"
SUB_ISSUE_PARENT_TITLE_KEY = "_dl_gh_project_sub_issue_parent_title"
SUB_ISSUE_PARENT_KEY_KEY = "_dl_gh_project_sub_issue_parent_key"
MAX_IMAGE_BYTES = 100 * 1024 * 1024

KNOWN_IMAGE_EXTENSIONS = {
    ".avif",
    ".bmp",
    ".gif",
    ".heic",
    ".heif",
    ".ico",
    ".jpeg",
    ".jpg",
    ".png",
    ".svg",
    ".tif",
    ".tiff",
    ".webp",
}

IMAGE_CONTENT_TYPE_EXTENSIONS = {
    "image/avif": ".avif",
    "image/bmp": ".bmp",
    "image/gif": ".gif",
    "image/heic": ".heic",
    "image/heif": ".heif",
    "image/jpeg": ".jpg",
    "image/png": ".png",
    "image/svg+xml": ".svg",
    "image/tiff": ".tiff",
    "image/vnd.microsoft.icon": ".ico",
    "image/webp": ".webp",
    "image/x-icon": ".ico",
}

GENERATED_IMAGE_FILENAME_RE = re.compile(r"[0-9]{6}\.[A-Za-z0-9]+")
GENERATED_IMAGE_TEMP_FILENAME_RE = re.compile(r"\.[0-9]{6}\.[A-Za-z0-9]+\.part")


class GitHubAPIError(RuntimeError):
    """Raised when GitHub returns an API error or the API response is invalid."""


@dataclass(frozen=True)
class ProjectURL:
    scope: str  # "orgs" or "users"
    owner: str
    number: int
    view_number: int | None


@dataclass(frozen=True)
class IssueReference:
    owner: str
    repo: str
    number: int

    @property
    def key(self) -> tuple[str, str, int]:
        return self.owner.lower(), self.repo.lower(), self.number

    @property
    def label(self) -> str:
        return f"{self.owner}/{self.repo}#{self.number}"


def owner_is_whitelisted(
    owner: str,
    owner_whitelist: frozenset[str] | None,
) -> bool:
    """Return whether recursive discovery may enter repositories owned by ``owner``."""

    return owner_whitelist is None or owner.casefold() in owner_whitelist


def is_trusted_github_host(hostname: str | None) -> bool:
    """Return whether an HTTP host is controlled by GitHub.

    Image requests may carry the user's token so private issue attachments can
    be downloaded. Restricting the token to GitHub-owned hosts prevents it from
    being sent to arbitrary external image servers or leaked by redirects.
    """

    host = str(hostname or "").rstrip(".").lower()
    return (
        host == "github.com"
        or host.endswith(".github.com")
        or host == "githubusercontent.com"
        or host.endswith(".githubusercontent.com")
        or host == "githubassets.com"
        or host.endswith(".githubassets.com")
    )


class SafeGitHubRedirectHandler(HTTPRedirectHandler):
    """Drop Authorization when an image redirect leaves GitHub-owned hosts."""

    def redirect_request(
        self,
        req: Request,
        fp: Any,
        code: int,
        msg: str,
        headers: Any,
        newurl: str,
    ) -> Request | None:
        redirected = super().redirect_request(req, fp, code, msg, headers, newurl)
        if redirected is not None and not is_trusted_github_host(urlparse(newurl).hostname):
            redirected.remove_header("Authorization")
        return redirected


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
            "  3. Select the repositories containing the Project's issue / PR cards and any issues / PRs they reference.\n"
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
    def __init__(self, token: str, *, request_spacing: float = 0.0) -> None:
        self.token = token
        self.request_spacing = max(0.0, float(request_spacing))
        self._request_schedule_lock = threading.Lock()
        self._next_request_at = 0.0

    def _wait_for_request_slot(self) -> None:
        """Pace request starts across worker threads."""

        while True:
            with self._request_schedule_lock:
                now = time.monotonic()
                delay = self._next_request_at - now
                if delay <= 0:
                    self._next_request_at = now + self.request_spacing
                    return
            time.sleep(delay)

    def _defer_requests(self, delay: float) -> None:
        with self._request_schedule_lock:
            self._next_request_at = max(
                self._next_request_at,
                time.monotonic() + max(0.0, float(delay)),
            )

    @staticmethod
    def _header_float(headers: Any, name: str) -> float | None:
        value = headers.get(name) if headers is not None else None
        if value is None:
            return None
        try:
            return float(value)
        except (TypeError, ValueError):
            return None

    def _http_retry_delay(self, exc: HTTPError, raw: str, attempt: int) -> float | None:
        """Return a retry delay for transient or rate-limit HTTP failures."""

        status = int(exc.code)
        retry_after = self._header_float(exc.headers, "Retry-After")
        if retry_after is not None:
            return max(0.0, retry_after)

        remaining = str(exc.headers.get("X-RateLimit-Remaining") or "")
        reset_epoch = self._header_float(exc.headers, "X-RateLimit-Reset")
        if status in {403, 429} and remaining == "0" and reset_epoch is not None:
            return max(1.0, reset_epoch - time.time() + 1.0)

        lowered = raw.casefold()
        if status in {403, 429} and (
            "secondary rate limit" in lowered
            or "abuse detection" in lowered
            or status == 429
        ):
            return min(60.0 * (2**attempt), 15.0 * 60.0)

        if 500 <= status <= 599:
            return min(2.0**attempt, 30.0)

        return None

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

        for attempt in range(MAX_API_RETRIES + 1):
            self._wait_for_request_slot()
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
                retry_delay = self._http_retry_delay(exc, raw, attempt)
                if retry_delay is None or attempt >= MAX_API_RETRIES:
                    message = self._format_http_error(method, url, exc, raw)
                    raise GitHubAPIError(message) from exc

                self._defer_requests(retry_delay)
                tqdm.write(
                    f"warning: {method} {safe_url_for_log(url)} returned HTTP {exc.code}; "
                    f"retrying after {retry_delay:.1f}s",
                    file=sys.stderr,
                )
            except URLError as exc:
                if attempt >= MAX_API_RETRIES:
                    raise GitHubAPIError(f"{method} {url} failed: {exc.reason}") from exc
                retry_delay = min(2.0**attempt, 30.0)
                self._defer_requests(retry_delay)
                tqdm.write(
                    f"warning: {method} {safe_url_for_log(url)} failed: {exc.reason}; "
                    f"retrying after {retry_delay:.1f}s",
                    file=sys.stderr,
                )
            except json.JSONDecodeError as exc:
                raise GitHubAPIError(f"{method} {url} returned invalid JSON") from exc

        raise AssertionError("unreachable request retry loop")

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

    def rest_get(
        self,
        path: str,
        *,
        params: dict[str, Any] | None = None,
    ) -> Any:
        """Return one REST response payload."""

        payload, _headers = self._request_json("GET", path, params=params)
        return payload

    def download_bytes(
        self,
        url: str,
        *,
        max_bytes: int = MAX_IMAGE_BYTES,
    ) -> tuple[bytes, Any, str]:
        """Download a remote image, authenticating only to GitHub-owned hosts."""

        parsed = urlparse(url)
        if parsed.scheme not in {"http", "https"} or not parsed.netloc:
            raise GitHubAPIError(f"unsupported image URL: {safe_url_for_log(url)}")

        headers = {
            "Accept": "image/*,application/octet-stream;q=0.9,*/*;q=0.1",
            "User-Agent": USER_AGENT,
        }
        if is_trusted_github_host(parsed.hostname):
            headers["Authorization"] = f"Bearer {self.token}"
            headers["X-GitHub-Api-Version"] = API_VERSION

        request = Request(url, headers=headers, method="GET")
        opener = build_opener(SafeGitHubRedirectHandler())

        try:
            with opener.open(request, timeout=60) as response:
                content_length = response.headers.get("Content-Length")
                if content_length:
                    try:
                        if int(content_length) > max_bytes:
                            raise GitHubAPIError(
                                f"image is larger than {max_bytes} bytes: {safe_url_for_log(url)}"
                            )
                    except ValueError:
                        pass

                payload = response.read(max_bytes + 1)
                if len(payload) > max_bytes:
                    raise GitHubAPIError(
                        f"image is larger than {max_bytes} bytes: {safe_url_for_log(url)}"
                    )
                return payload, response.headers, response.geturl()
        except HTTPError as exc:
            raise GitHubAPIError(
                f"GET {safe_url_for_log(url)} failed: HTTP {exc.code} {exc.reason}"
            ) from exc
        except URLError as exc:
            raise GitHubAPIError(
                f"GET {safe_url_for_log(url)} failed: {exc.reason}"
            ) from exc

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


def get_repository_issue(
    client: GitHubClient,
    owner: str,
    repo: str,
    issue_number: int,
) -> dict[str, Any]:
    """Return one issue or pull request through the REST issues endpoint."""

    owner_q = quote(owner, safe="")
    repo_q = quote(repo, safe="")
    path = f"/repos/{owner_q}/{repo_q}/issues/{issue_number}"
    payload = client.rest_get(path)
    if not isinstance(payload, dict):
        raise GitHubAPIError(
            f"GET {path} did not return an issue object"
        )
    return payload


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

    entry = {
        "kind": "comment" if is_comment else "event",
        "login": login,
        "created_at": created_at,
        "body": event.get("body") or "" if is_comment else event_body_for_rest_event(event, tz, anchor_by_key),
        "dedupe_key": f"rest:{identifier}",
    }
    if not is_comment:
        entry["_rest_event"] = event
    return entry


def rendered_timeline_entry_body(
    entry: dict[str, Any],
    tz: ZoneInfo,
    anchor_by_key: dict[tuple[str, str, int], str],
) -> str:
    """Render a cached timeline entry with the final local issue anchors."""

    rest_event = entry.get("_rest_event")
    if entry.get("kind") == "event" and isinstance(rest_event, dict):
        return event_body_for_rest_event(rest_event, tz, anchor_by_key)
    return str(entry.get("body") or "")


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


def timeline_entries_for_item(
    client: GitHubClient,
    item: dict[str, Any],
    tz: ZoneInfo,
) -> list[dict[str, Any]]:
    """Return and cache all rendered timeline entries for one exported item.

    Reference discovery runs before heading anchors are known, so cross-reference
    events initially use absolute GitHub URLs. The normal final rendering pass
    still converts shorthand references to local anchors where possible.
    """

    cached = item.get(TIMELINE_ENTRIES_KEY)
    if isinstance(cached, list):
        return cached

    issue = item.get("content")
    if not isinstance(issue, dict):
        entries: list[dict[str, Any]] = []
    elif is_draft_issue(issue):
        entries = collect_draft_timeline_entries(item, issue)
    else:
        details = issue_repository_details(issue)
        if not details:
            entries = []
        else:
            repo_owner, repo_name, issue_number = details
            entries = collect_issue_timeline_entries(
                client,
                str(repo_owner),
                str(repo_name),
                int(issue_number),
                issue,
                tz,
                {},
            )

    item[TIMELINE_ENTRIES_KEY] = entries
    return entries


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
    if column_key == REFERENCED_SECTION_KEY:
        return REFERENCED_COLUMN_NAME
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
    inline Markdown forms whose visible text is what GitHub uses for the slug,
    then decodes character references as the Markdown renderer would.
    """
    text = str(value or "")
    text = re.sub(r"!\[([^\]]*)\]\([^)]*\)", r"\1", text)
    text = re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", text)
    text = re.sub(r"`([^`]*)`", r"\1", text)
    text = re.sub(r"<[^>]+>", "", text)
    return html.unescape(text)


def github_heading_slug_character_is_kept(character: str) -> bool:
    """Return whether GitHub keeps ``character`` in a heading slug.

    GitHub retains letters, combining marks, decimal / letter numbers,
    connector punctuation, the ordinary ASCII hyphen, and ordinary spaces.
    Most other punctuation, symbols, controls, and separators are removed.
    A small set of alphabetic symbols is retained by GitHub; NFKC-to-one-letter
    symbols cover the common enclosed-letter cases without a large lookup table.
    """

    if character in {" ", "-"}:
        return True

    category = unicodedata.category(character)
    if category[0] in {"L", "M"} or category in {"Nd", "Nl", "Pc"}:
        return True

    if category[0] == "S":
        normalized = unicodedata.normalize("NFKC", character)
        return len(normalized) == 1 and normalized.isalpha()

    return False


def github_heading_slug(value: str) -> str:
    """Return a GitHub-style slug for a Markdown heading.

    Each retained ordinary space becomes one hyphen. Spaces are deliberately
    not collapsed: punctuation between two spaces is removed first, so a
    heading such as ``A – B`` becomes ``a--b``.
    """

    text = markdown_heading_plain_text(value).lower()
    retained = "".join(
        character
        for character in text
        if github_heading_slug_character_is_kept(character)
    )
    return retained.replace(" ", "-")


class HeadingAnchorTracker:
    """Track unique GitHub-style heading anchors in render order."""

    def __init__(self) -> None:
        self._occurrences: dict[str, int] = {}

    def anchor_for(self, heading: str) -> str:
        slug = github_heading_slug(heading)
        original_slug = slug

        # Collision checks must include already-generated suffixed anchors. For
        # example, headings ``echo``, ``echo``, and ``echo 1`` become
        # ``echo``, ``echo-1``, and ``echo-1-1`` rather than duplicating
        # ``echo-1``.
        while slug in self._occurrences:
            self._occurrences[original_slug] += 1
            slug = f"{original_slug}-{self._occurrences[original_slug]}"

        self._occurrences[slug] = 0
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
    ranges = markdown_code_protected_ranges(markdown)

    protected_patterns = [
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


def markdown_code_protected_ranges(markdown: str) -> list[tuple[int, int]]:
    """Return fenced- and inline-code ranges in Markdown."""

    ranges = fenced_code_block_ranges(markdown)
    for match in re.finditer(r"(?s)(`+)(?:(?!\1).)*\1", markdown):
        ranges.append(match.span())
    return merge_ranges(ranges, len(markdown))


def unprotected_markdown_segments(
    markdown: str,
    protected_ranges: list[tuple[int, int]],
) -> Iterator[str]:
    """Yield text outside sorted protected Markdown ranges."""

    for _start, _end, segment in unprotected_markdown_spans(markdown, protected_ranges):
        yield segment


def unprotected_markdown_spans(
    markdown: str,
    protected_ranges: list[tuple[int, int]],
) -> Iterator[tuple[int, int, str]]:
    """Yield start, end, and text outside sorted protected Markdown ranges."""

    cursor = 0
    for start, end in protected_ranges:
        if cursor < start:
            yield cursor, start, markdown[cursor:start]
        cursor = max(cursor, end)
    if cursor < len(markdown):
        yield cursor, len(markdown), markdown[cursor:]


GITHUB_WEB_ISSUE_URL_RE = re.compile(
    r"(?<![A-Za-z0-9_.-])(?:https?:)?//(?:(?:www|redirect)\.)?github\.com/"
    r"(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+)/"
    r"(?:issues|pull)/(?P<number>[1-9][0-9]*)\b",
    flags=re.IGNORECASE,
)

GITHUB_API_ISSUE_URL_RE = re.compile(
    r"(?<![A-Za-z0-9_.-])(?:https?:)?//api\.github\.com/repos/"
    r"(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+)/"
    r"(?:issues|pulls)/(?P<number>[1-9][0-9]*)\b",
    flags=re.IGNORECASE,
)

SHORT_ISSUE_REFERENCE_RE = re.compile(
    r"(?<![\\\w./-])"
    r"(?:"
    r"(?:(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+))?"
    r"#(?P<number>[1-9][0-9]*)"
    r"|"
    r"GH-(?P<gh_number>[1-9][0-9]*)"
    r")\b",
    flags=re.IGNORECASE,
)

RELATIVE_ISSUE_PATH_RE = re.compile(
    r"(?<![A-Za-z0-9_.-])"
    r"(?P<path>"
    r"(?:(?:\.\.?/)+|/)?"
    r"(?:(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+)/)?"
    r"(?:issues|pull)/(?P<number>[1-9][0-9]*)"
    r")\b",
    flags=re.IGNORECASE,
)

ABSOLUTE_URL_RE = re.compile(r"(?:https?:)?//[^\s<>)\]]+", flags=re.IGNORECASE)


def issue_references_in_markdown(
    markdown: str,
    current_issue: dict[str, Any] | None = None,
) -> list[IssueReference]:
    """Return GitHub issue/PR references in first-appearance order.

    Full and relative GitHub issue and pull-request URLs are recognized inside
    Markdown links. Shorthand references are recognized only outside code,
    links, raw URLs, and HTML tags so local fragments such as
    ``](#123-heading)`` are not mistaken for issue numbers.
    """

    if not markdown:
        return []

    current_owner = None
    current_repo = None
    if isinstance(current_issue, dict):
        details = issue_repository_details(current_issue)
        if details:
            current_owner, current_repo, _number = details

    references: list[IssueReference] = []
    seen: set[tuple[str, str, int]] = set()

    def add(owner: str, repo: str, number_text: str) -> None:
        try:
            number = int(number_text)
        except (TypeError, ValueError):
            return
        owner = unquote(owner).strip()
        repo = unquote(repo).strip()
        if not owner or not repo or number < 1:
            return
        key = (owner.lower(), repo.lower(), number)
        if key not in seen:
            seen.add(key)
            references.append(IssueReference(owner, repo, number))

    candidates: list[tuple[int, str, str, str]] = []

    # URLs in link destinations are meaningful references, but code samples are not.
    for segment_start, _segment_end, segment in unprotected_markdown_spans(
        markdown,
        markdown_code_protected_ranges(markdown),
    ):
        for pattern in (GITHUB_WEB_ISSUE_URL_RE, GITHUB_API_ISSUE_URL_RE):
            for match in pattern.finditer(segment):
                candidates.append(
                    (
                        segment_start + match.start(),
                        match.group("owner"),
                        match.group("repo"),
                        match.group("number"),
                    )
                )

        absolute_url_ranges = [match.span() for match in ABSOLUTE_URL_RE.finditer(segment)]
        for match in RELATIVE_ISSUE_PATH_RE.finditer(segment):
            if any(start <= match.start() < end for start, end in absolute_url_ranges):
                continue
            owner = match.group("owner") or current_owner
            repo = match.group("repo") or current_repo
            if owner and repo:
                candidates.append(
                    (
                        segment_start + match.start(),
                        str(owner),
                        str(repo),
                        match.group("number"),
                    )
                )

    # Existing Markdown links and URLs are protected here because their URL pass
    # above already handled genuine GitHub targets.
    for segment_start, _segment_end, segment in unprotected_markdown_spans(
        markdown,
        markdown_link_protected_ranges(markdown),
    ):
        for match in SHORT_ISSUE_REFERENCE_RE.finditer(segment):
            owner = match.group("owner") or current_owner
            repo = match.group("repo") or current_repo
            number_text = match.group("number") or match.group("gh_number")
            if owner and repo:
                candidates.append(
                    (
                        segment_start + match.start(),
                        str(owner),
                        str(repo),
                        str(number_text),
                    )
                )

    for _position, owner, repo, number_text in sorted(candidates, key=lambda item: item[0]):
        add(owner, repo, number_text)

    return references


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
    def replacement(match: re.Match[str]) -> str:
        number_text = match.group("number") or match.group("gh_number")
        owner = match.group("owner") or repo_owner
        repo = match.group("repo") or repo_name
        if not owner or not repo:
            return match.group(0)

        number = int(number_text)
        key = (owner.lower(), repo.lower(), number)
        anchor = anchor_by_key.get(key)
        target = f"#{anchor}" if anchor else github_issue_url(owner, repo, number)
        return f"[{markdown_link_text(match.group(0))}]({target})"

    return SHORT_ISSUE_REFERENCE_RE.sub(replacement, segment)


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


INLINE_MARKDOWN_IMAGE_RE = re.compile(
    r"!\[(?P<alt>(?:\\.|[^\\\]])*)\]\("
    r"(?P<leading>[ \t]*)"
    r"(?P<destination><[^>\n]*>|(?:\\.|[^()\s\n]|\([^()\n]*\))+?)"
    r"(?P<suffix>(?:[ \t]+(?:\"(?:\\.|[^\"])*\"|'(?:\\.|[^'])*'|\((?:\\.|[^)])*\)))?[ \t]*)"
    r"\)"
)

EXPLICIT_REFERENCE_IMAGE_RE = re.compile(
    r"!\[(?P<alt>(?:\\.|[^\\\]])*)\]\[(?P<label>[^\]\n]*)\]"
)

SHORTCUT_REFERENCE_IMAGE_RE = re.compile(
    r"!\[(?P<alt>(?:\\.|[^\\\]])*)\](?![ \t]*[\[(])"
)

REFERENCE_DEFINITION_RE = re.compile(
    r"(?m)^(?P<prefix> {0,3}\[(?P<label>[^\]\n]+)\]:[ \t]*)"
    r"(?P<destination><[^>\n]+>|(?:\\.|[^\s\n])+)(?P<suffix>[^\n]*)$"
)

HTML_IMAGE_TAG_RE = re.compile(r"<(?:img|source)\b[^>]*>", re.IGNORECASE)

HTML_IMAGE_ATTRIBUTE_RE = re.compile(
    r"(?<![A-Za-z0-9_:-])"
    r"(?P<prefix>(?P<name>src|srcset)[ \t]*=[ \t]*)"
    r"(?:\"(?P<double>[^\"]*)\"|'(?P<single>[^']*)'|(?P<bare>[^\s>]+))",
    re.IGNORECASE,
)


def normalized_reference_label(value: str) -> str:
    """Normalize a Markdown reference label using CommonMark-style whitespace rules."""

    return re.sub(r"\s+", " ", str(value or "")).strip().casefold()


def markdown_image_reference_labels(markdown: str) -> set[str]:
    """Return reference-definition labels that are used by images."""

    labels: set[str] = set()
    for segment in unprotected_markdown_segments(
        markdown,
        markdown_code_protected_ranges(markdown),
    ):
        for match in EXPLICIT_REFERENCE_IMAGE_RE.finditer(segment):
            label = match.group("label") or match.group("alt")
            normalized = normalized_reference_label(label)
            if normalized:
                labels.add(normalized)

        for match in SHORTCUT_REFERENCE_IMAGE_RE.finditer(segment):
            normalized = normalized_reference_label(match.group("alt"))
            if normalized:
                labels.add(normalized)

    return labels


def markdown_unescape_destination(value: str) -> str:
    """Remove backslash escapes that are valid in a Markdown link destination."""

    return re.sub(r"\\([\\`*{}\[\]()#+\-.!_>])", r"\1", value)


def safe_url_for_log(url: str) -> str:
    """Remove query strings and fragments that may contain signed asset credentials."""

    parsed = urlparse(str(url))
    if not parsed.scheme or not parsed.netloc:
        return str(url)
    return urlunparse((parsed.scheme, parsed.netloc, parsed.path, "", "", ""))


def content_type_from_headers(headers: Any) -> str:
    """Return a normalized response Content-Type without parameters."""

    if hasattr(headers, "get_content_type"):
        try:
            return str(headers.get_content_type() or "").lower()
        except (AttributeError, TypeError):
            pass
    value = headers.get("Content-Type") if hasattr(headers, "get") else None
    return str(value or "").split(";", 1)[0].strip().lower()


def normalized_image_extension(value: str | None) -> str | None:
    """Return a safe, conventional image suffix."""

    suffix = str(value or "").lower()
    if suffix == ".jpe":
        suffix = ".jpg"
    if suffix in KNOWN_IMAGE_EXTENSIONS:
        return suffix
    return None


def image_extension_from_url(url: str) -> str | None:
    path = unquote(urlparse(url).path)
    return normalized_image_extension(Path(path).suffix)


def image_extension_from_headers(headers: Any) -> str | None:
    """Return an image suffix from Content-Disposition, when available."""

    if hasattr(headers, "get_filename"):
        try:
            filename = headers.get_filename()
        except (AttributeError, TypeError):
            filename = None
        if filename:
            return normalized_image_extension(Path(str(filename)).suffix)
    return None


def sniff_image_extension(payload: bytes) -> str | None:
    """Identify common image formats from their file signatures."""

    if payload.startswith(b"\x89PNG\r\n\x1a\n"):
        return ".png"
    if payload.startswith(b"\xff\xd8\xff"):
        return ".jpg"
    if payload.startswith((b"GIF87a", b"GIF89a")):
        return ".gif"
    if payload.startswith(b"BM"):
        return ".bmp"
    if payload.startswith((b"II*\x00", b"MM\x00*")):
        return ".tiff"
    if payload.startswith(b"\x00\x00\x01\x00"):
        return ".ico"
    if len(payload) >= 12 and payload[:4] == b"RIFF" and payload[8:12] == b"WEBP":
        return ".webp"
    if len(payload) >= 12 and payload[4:8] == b"ftyp":
        brand = payload[8:12]
        if brand in {b"avif", b"avis"}:
            return ".avif"
        if brand in {b"heic", b"heix", b"hevc", b"hevx", b"mif1", b"msf1"}:
            return ".heic"

    head = payload[:4096].lstrip().lower()
    if head.startswith(b"<svg") or (head.startswith(b"<?xml") and b"<svg" in head):
        return ".svg"
    return None


def choose_image_extension(payload: bytes, headers: Any, final_url: str, source_url: str) -> str:
    """Choose an image suffix from bytes, MIME type, and URL metadata."""

    sniffed = sniff_image_extension(payload)
    if sniffed:
        return sniffed

    content_type = content_type_from_headers(headers)
    mapped = IMAGE_CONTENT_TYPE_EXTENSIONS.get(content_type)
    if mapped:
        return mapped

    guessed = normalized_image_extension(mimetypes.guess_extension(content_type))
    if guessed:
        return guessed

    return (
        image_extension_from_headers(headers)
        or image_extension_from_url(final_url)
        or image_extension_from_url(source_url)
        or ".img"
    )


def validate_image_download(payload: bytes, headers: Any, final_url: str, source_url: str) -> None:
    """Reject empty downloads and common HTML error/login responses."""

    if not payload:
        raise GitHubAPIError(f"downloaded image was empty: {safe_url_for_log(source_url)}")

    content_type = content_type_from_headers(headers)
    sniffed = sniff_image_extension(payload)
    header_extension = image_extension_from_headers(headers)
    url_extension = image_extension_from_url(final_url) or image_extension_from_url(source_url)
    head = payload[:1024].lstrip().lower()
    looks_like_html = head.startswith(b"<!doctype html") or head.startswith(b"<html")
    known_non_image_type = content_type in {
        "application/json",
        "application/xhtml+xml",
        "text/html",
    }

    if looks_like_html or known_non_image_type:
        raise GitHubAPIError(
            f"image URL returned {content_type or 'HTML'} instead of an image: "
            f"{safe_url_for_log(source_url)}"
        )
    if not content_type.startswith("image/") and not sniffed and not header_extension and not url_extension:
        raise GitHubAPIError(
            f"URL did not return recognizable image data: {safe_url_for_log(source_url)}"
        )


def resolve_remote_image_url(raw_url: str, issue: dict[str, Any] | None) -> str | None:
    """Resolve an embedded image URL against its GitHub issue page."""

    value = html.unescape(markdown_unescape_destination(str(raw_url or "").strip()))
    if not value:
        return None
    if value.startswith("<") and value.endswith(">"):
        value = value[1:-1].strip()
    if not value or value.startswith("#"):
        return None

    parsed = urlparse(value)
    if parsed.scheme.lower() in {"data", "cid", "file", "javascript", "mailto"}:
        return None
    if value.startswith("//"):
        return "https:" + value
    if parsed.scheme:
        return value if parsed.scheme.lower() in {"http", "https"} else None

    base_url = issue_url(issue) if isinstance(issue, dict) else None
    if not base_url:
        return None
    return urljoin(base_url, value)


class ImageLocalizer:
    """Download embedded images once and rewrite each occurrence to a local path."""

    def __init__(self, client: GitHubClient, output_path: Path) -> None:
        self.client = client
        self.output_path = output_path
        self.image_directory = output_path.parent / f"{output_path.stem} (images)"
        self.relative_directory_name = self.image_directory.name
        self._local_by_url: dict[str, str] = {}
        self._failed_urls: set[str] = set()
        self._current_filenames: set[str] = set()
        self.images_downloaded = 0
        self.image_references_rewritten = 0
        self.image_references_reused = 0
        self.image_download_failures = 0

    def stats(self) -> dict[str, int | str]:
        return {
            "images_downloaded": self.images_downloaded,
            "image_references_rewritten": self.image_references_rewritten,
            "image_references_reused": self.image_references_reused,
            "image_download_failures": self.image_download_failures,
            "image_directory": str(self.image_directory),
        }

    def localize_url(self, raw_url: str, issue: dict[str, Any] | None) -> str | None:
        value = html.unescape(str(raw_url or "").strip())
        local_prefix = self.relative_directory_name + "/"
        encoded_local_prefix = quote(self.relative_directory_name, safe="()") + "/"
        if (
            value.startswith(local_prefix)
            or value.startswith("<" + local_prefix)
            or value.startswith(encoded_local_prefix)
            or value.startswith("<" + encoded_local_prefix)
        ):
            local_reference = unquote(value.strip("<>"))
            filename = Path(local_reference).name
            if GENERATED_IMAGE_FILENAME_RE.fullmatch(filename):
                self._current_filenames.add(filename)
            return local_reference

        remote_url = resolve_remote_image_url(value, issue)
        if not remote_url:
            return None

        cached = self._local_by_url.get(remote_url)
        if cached:
            self.image_references_reused += 1
            return cached
        if remote_url in self._failed_urls:
            self.image_references_reused += 1
            return None

        temporary: Path | None = None
        try:
            payload, headers, final_url = self.client.download_bytes(remote_url)
            validate_image_download(payload, headers, final_url, remote_url)
            extension = choose_image_extension(payload, headers, final_url, remote_url)

            filename = f"{self.images_downloaded + 1:06d}{extension}"
            self.image_directory.mkdir(parents=True, exist_ok=True)
            destination = self.image_directory / filename
            temporary = self.image_directory / f".{filename}.part"
            temporary.write_bytes(payload)
            temporary.replace(destination)

            local_reference = f"{self.relative_directory_name}/{filename}"
            self._local_by_url[remote_url] = local_reference
            self._local_by_url.setdefault(final_url, local_reference)
            self._current_filenames.add(filename)
            self.images_downloaded += 1
            return local_reference
        except (GitHubAPIError, OSError, ValueError) as exc:
            if temporary is not None:
                try:
                    temporary.unlink(missing_ok=True)
                except OSError:
                    pass
            self._failed_urls.add(remote_url)
            self.image_download_failures += 1
            print(
                f"warning: could not download embedded image {safe_url_for_log(remote_url)}: {exc}",
                file=sys.stderr,
            )
            return None

    def finalize(self) -> None:
        """Remove numbered image files left over from an earlier export."""

        if not self.image_directory.exists():
            return

        for child in self.image_directory.iterdir():
            if child.is_file() and GENERATED_IMAGE_TEMP_FILENAME_RE.fullmatch(child.name):
                child.unlink()
                continue
            if (
                child.is_file()
                and GENERATED_IMAGE_FILENAME_RE.fullmatch(child.name)
                and child.name not in self._current_filenames
            ):
                child.unlink()

        try:
            next(self.image_directory.iterdir())
        except StopIteration:
            self.image_directory.rmdir()

    def _rewrite_inline_images(self, segment: str, issue: dict[str, Any] | None) -> str:
        def replacement(match: re.Match[str]) -> str:
            destination = match.group("destination")
            raw_url = destination[1:-1] if destination.startswith("<") and destination.endswith(">") else destination
            local_reference = self.localize_url(raw_url, issue)
            if not local_reference:
                return match.group(0)
            self.image_references_rewritten += 1
            return (
                f"![{match.group('alt')}]("
                f"<{local_reference}>"
                f"{match.group('suffix')})"
            )

        return INLINE_MARKDOWN_IMAGE_RE.sub(replacement, segment)

    def _rewrite_reference_definitions(
        self,
        segment: str,
        issue: dict[str, Any] | None,
        image_labels: set[str],
    ) -> str:
        def replacement(match: re.Match[str]) -> str:
            if normalized_reference_label(match.group("label")) not in image_labels:
                return match.group(0)
            destination = match.group("destination")
            raw_url = destination[1:-1] if destination.startswith("<") and destination.endswith(">") else destination
            local_reference = self.localize_url(raw_url, issue)
            if not local_reference:
                return match.group(0)
            self.image_references_rewritten += 1
            return f"{match.group('prefix')}<{local_reference}>{match.group('suffix')}"

        return REFERENCE_DEFINITION_RE.sub(replacement, segment)

    def _rewrite_srcset(self, value: str, issue: dict[str, Any] | None) -> str:
        if value.lstrip().lower().startswith("data:"):
            return value

        rewritten: list[str] = []
        changed = False
        for candidate in value.split(","):
            stripped = candidate.strip()
            if not stripped:
                continue
            pieces = stripped.split(None, 1)
            local_reference = self.localize_url(pieces[0], issue)
            if local_reference:
                # Spaces delimit candidates/descriptors in srcset, so encode
                # them even though ordinary quoted src attributes can retain
                # the literal local path.
                pieces[0] = quote(local_reference, safe="/()")
                changed = True
                self.image_references_rewritten += 1
            rewritten.append(" ".join(pieces))
        return ", ".join(rewritten) if changed else value

    def _rewrite_html_images(self, segment: str, issue: dict[str, Any] | None) -> str:
        def tag_replacement(tag_match: re.Match[str]) -> str:
            tag = tag_match.group(0)

            def attribute_replacement(attribute_match: re.Match[str]) -> str:
                value = (
                    attribute_match.group("double")
                    if attribute_match.group("double") is not None
                    else attribute_match.group("single")
                    if attribute_match.group("single") is not None
                    else attribute_match.group("bare")
                    or ""
                )
                if attribute_match.group("name").lower() == "srcset":
                    rewritten = self._rewrite_srcset(html.unescape(value), issue)
                else:
                    decoded_value = html.unescape(value)
                    local_reference = self.localize_url(decoded_value, issue)
                    rewritten = local_reference or decoded_value
                    if local_reference:
                        self.image_references_rewritten += 1

                escaped = html.escape(rewritten, quote=True)
                return f"{attribute_match.group('prefix')}\"{escaped}\""

            return HTML_IMAGE_ATTRIBUTE_RE.sub(attribute_replacement, tag)

        return HTML_IMAGE_TAG_RE.sub(tag_replacement, segment)

    def localize_markdown(self, markdown: str, issue: dict[str, Any] | None) -> str:
        if not markdown:
            return markdown

        image_labels = markdown_image_reference_labels(markdown)
        ranges = markdown_code_protected_ranges(markdown)
        pieces: list[str] = []
        cursor = 0

        for start, end in ranges:
            if cursor < start:
                pieces.append(self._localize_segment(markdown[cursor:start], issue, image_labels))
            pieces.append(markdown[start:end])
            cursor = end

        if cursor < len(markdown):
            pieces.append(self._localize_segment(markdown[cursor:], issue, image_labels))
        return "".join(pieces)

    def _localize_segment(
        self,
        segment: str,
        issue: dict[str, Any] | None,
        image_labels: set[str],
    ) -> str:
        segment = self._rewrite_reference_definitions(segment, issue, image_labels)
        segment = self._rewrite_inline_images(segment, issue)
        return self._rewrite_html_images(segment, issue)


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


def synthetic_referenced_issue_item(issue: dict[str, Any]) -> dict[str, Any]:
    """Return a synthetic Project-like item for a recursively referenced issue."""

    return {
        "id": f"referenced:{issue.get('id') or issue.get('url') or issue.get('number')}",
        "type": "PULL_REQUEST" if issue.get("__typename") == "PullRequest" else "ISSUE",
        "isArchived": False,
        "content": issue,
        REFERENCED_ITEM_KEY: True,
    }


def issue_references_for_item(
    client: GitHubClient,
    item: dict[str, Any],
    tz: ZoneInfo,
) -> list[IssueReference]:
    """Return all issue/PR references visible in one item's exported content."""

    issue = item.get("content")
    if not isinstance(issue, dict):
        return []

    references: list[IssueReference] = []
    seen: set[tuple[str, str, int]] = set()

    def add_reference(reference: IssueReference) -> None:
        if reference.key not in seen:
            seen.add(reference.key)
            references.append(reference)

    def add_from(markdown: str) -> None:
        for reference in issue_references_in_markdown(markdown, issue):
            add_reference(reference)

    add_from(str(issue.get("title") or ""))
    for entry in timeline_entries_for_item(client, item, tz):
        add_from(str(entry.get("body") or ""))
        rest_event = entry.get("_rest_event")
        source = rest_event.get("source") if isinstance(rest_event, dict) else None
        source_issue = source.get("issue") if isinstance(source, dict) else None
        if isinstance(source_issue, dict):
            details = issue_repository_details(source_issue)
            if details:
                add_reference(IssueReference(*details))

    return references


def item_progress_label(item: dict[str, Any]) -> str:
    """Return a compact issue label for progress displays."""

    key = issue_key_for_item(item)
    content = item.get("content")
    if key:
        return f"{key[0]}/{key[1]}#{key[2]}"
    if isinstance(content, dict) and is_draft_issue(content):
        return "draft"
    return "unknown"


def add_referenced_issues_to_grouped_items(
    client: GitHubClient,
    grouped: OrderedDict[str, list[dict[str, Any]]],
    tz: ZoneInfo,
    attempted_reference_keys: set[tuple[str, str, int]] | None = None,
    pass_number: int = 1,
    workers: int = DEFAULT_WORKERS,
    owner_whitelist: frozenset[str] | None = None,
    skipped_reference_keys: set[tuple[str, str, int]] | None = None,
) -> tuple[OrderedDict[str, list[dict[str, Any]]], dict[str, int]]:
    """Recursively append missing referenced issues to a dedicated section.

    Histories for independent issues are fetched concurrently in bounded
    batches. References discovered in one batch are then fetched concurrently,
    appended in deterministic discovery order, and scanned in the next batch.

    When ``owner_whitelist`` is provided, a discovered reference is fetched only
    when its repository owner is in that case-insensitive whitelist. Project
    cards already present in ``grouped`` are never filtered by this option.
    """

    attempted = attempted_reference_keys if attempted_reference_keys is not None else set()
    skipped = skipped_reference_keys if skipped_reference_keys is not None else set()
    skipped_before = len(skipped)
    known_keys = project_item_issue_keys(grouped)
    queue = [
        item
        for items in grouped.values()
        for item in items
        if not item.get(REFERENCE_SCAN_COMPLETE_KEY)
    ]
    added = 0
    failures = 0
    queue_index = 0

    if not queue:
        return grouped, {
            "referenced_issue_items_exported": added,
            "referenced_issue_fetch_failures": failures,
            "referenced_issue_whitelist_skips": len(skipped) - skipped_before,
        }

    description = f"Issue histories and references (pass {pass_number})"
    with ThreadPoolExecutor(max_workers=workers, thread_name_prefix="gh-history") as executor:
        with tqdm(total=len(queue), desc=description, unit="issue") as progress:
            while queue_index < len(queue):
                batch = queue[queue_index:]
                queue_index = len(queue)
                scan_results: list[list[IssueReference] | None] = [None] * len(batch)
                future_to_index: dict[Future[list[IssueReference]], int] = {}

                for index, item in enumerate(batch):
                    future = executor.submit(issue_references_for_item, client, item, tz)
                    future_to_index[future] = index

                for future in as_completed(future_to_index):
                    index = future_to_index[future]
                    item = batch[index]
                    scan_results[index] = future.result()
                    item[REFERENCE_SCAN_COMPLETE_KEY] = True
                    progress.update(1)
                    progress.set_postfix(
                        phase="history",
                        current=item_progress_label(item),
                        found=added,
                        failed=failures,
                        blocked=len(skipped),
                        refresh=False,
                    )

                pending_by_key: OrderedDict[tuple[str, str, int], IssueReference] = OrderedDict()
                for references in scan_results:
                    for reference in references or []:
                        requested_key = reference.key
                        if (
                            requested_key in known_keys
                            or requested_key in attempted
                            or requested_key in skipped
                            or requested_key in pending_by_key
                        ):
                            continue
                        if not owner_is_whitelisted(reference.owner, owner_whitelist):
                            skipped.add(requested_key)
                            continue
                        attempted.add(requested_key)
                        pending_by_key[requested_key] = reference

                if not pending_by_key:
                    continue

                pending = list(pending_by_key.values())
                fetched: list[tuple[dict[str, Any] | None, GitHubAPIError | None]] = [
                    (None, None) for _ in pending
                ]
                fetch_future_to_index: dict[Future[dict[str, Any]], int] = {}

                for index, reference in enumerate(pending):
                    fetch_future_to_index[
                        executor.submit(
                            get_repository_issue,
                            client,
                            reference.owner,
                            reference.repo,
                            reference.number,
                        )
                    ] = index

                fetch_description = f"Referenced issue details (pass {pass_number})"
                with tqdm(
                    total=len(pending),
                    desc=fetch_description,
                    unit="issue",
                    leave=False,
                ) as fetch_progress:
                    for future in as_completed(fetch_future_to_index):
                        index = fetch_future_to_index[future]
                        reference = pending[index]
                        try:
                            rest_issue = future.result()
                            fetched[index] = (rest_issue, None)
                        except GitHubAPIError as exc:
                            fetched[index] = (None, exc)
                        fetch_progress.update(1)
                        fetch_progress.set_postfix(current=reference.label, refresh=False)

                for reference, (rest_issue, error) in zip(pending, fetched):
                    owner = reference.owner
                    repo = reference.repo
                    number = reference.number
                    if error is not None:
                        failures += 1
                        tqdm.write(
                            f"warning: could not load referenced issue {owner}/{repo}#{number}: {error}",
                            file=sys.stderr,
                        )
                        continue
                    if not isinstance(rest_issue, dict):
                        failures += 1
                        tqdm.write(
                            f"warning: referenced issue {owner}/{repo}#{number} returned no issue object",
                            file=sys.stderr,
                        )
                        continue

                    issue = rest_issue_to_project_content(rest_issue, owner, repo)
                    actual_key = issue_key(issue)
                    if not actual_key:
                        failures += 1
                        tqdm.write(
                            f"warning: referenced issue {owner}/{repo}#{number} had no stable repository/number identity",
                            file=sys.stderr,
                        )
                        continue

                    attempted.add(actual_key)
                    if actual_key in known_keys:
                        continue
                    if not owner_is_whitelisted(actual_key[0], owner_whitelist):
                        # GitHub can redirect a transferred issue to a different
                        # repository. Re-check the actual owner before adding it.
                        skipped.add(actual_key)
                        continue

                    referenced_item = synthetic_referenced_issue_item(issue)
                    grouped.setdefault(REFERENCED_SECTION_KEY, []).append(referenced_item)
                    ensure_archived_section_at_end(grouped)
                    known_keys.add(actual_key)
                    queue.append(referenced_item)
                    added += 1

                progress.total = len(queue)
                progress.set_postfix(
                    phase="references",
                    current="queued",
                    found=added,
                    failed=failures,
                    blocked=len(skipped),
                    refresh=False,
                )
                progress.refresh()

            progress.set_postfix(
                phase="done",
                current="done",
                found=added,
                failed=failures,
                blocked=len(skipped),
                refresh=True,
            )

    return grouped, {
        "referenced_issue_items_exported": added,
        "referenced_issue_fetch_failures": failures,
        "referenced_issue_whitelist_skips": len(skipped) - skipped_before,
    }

def fetch_direct_sub_issue_contents(
    client: GitHubClient,
    issue: dict[str, Any],
) -> list[dict[str, Any]]:
    """Load and normalize one issue's direct sub-issues."""

    if not issue_can_have_sub_issues(issue):
        return []

    details = issue_repository_details(issue)
    if not details:
        return []

    repo_owner, repo_name, issue_number = details
    sub_issues: list[dict[str, Any]] = []
    for sub_issue in iter_sub_issues(client, repo_owner, repo_name, issue_number):
        if isinstance(sub_issue, dict):
            sub_issues.append(
                rest_issue_to_project_content(sub_issue, repo_owner, repo_name)
            )
    return sub_issues


def prefetch_sub_issue_tree(
    client: GitHubClient,
    roots: list[dict[str, Any]],
    sub_issue_cache: dict[tuple[str, str, int], list[dict[str, Any]]],
    workers: int,
    pass_number: int,
) -> None:
    """Populate the direct-sub-issue cache in concurrent breadth-first waves."""

    queued: set[tuple[str, str, int]] = set(sub_issue_cache)
    frontier: list[dict[str, Any]] = []

    for issue in roots:
        key = issue_key(issue)
        if not key or key in queued or not issue_can_have_sub_issues(issue):
            continue
        queued.add(key)
        frontier.append(issue)

    if not frontier:
        return

    relationship_count = 0
    description = f"Sub-issue relationships (pass {pass_number})"
    with ThreadPoolExecutor(max_workers=workers, thread_name_prefix="gh-subissues") as executor:
        with tqdm(total=len(frontier), desc=description, unit="issue") as progress:
            while frontier:
                batch = frontier
                frontier = []
                results: list[list[dict[str, Any]] | None] = [None] * len(batch)
                future_to_index: dict[Future[list[dict[str, Any]]], int] = {}

                for index, issue in enumerate(batch):
                    future_to_index[
                        executor.submit(fetch_direct_sub_issue_contents, client, issue)
                    ] = index

                for future in as_completed(future_to_index):
                    index = future_to_index[future]
                    issue = batch[index]
                    results[index] = future.result()
                    progress.update(1)
                    details = issue_repository_details(issue)
                    current = (
                        f"{details[0]}/{details[1]}#{details[2]}"
                        if details
                        else "unknown"
                    )
                    progress.set_postfix(
                        current=current,
                        relationships=relationship_count,
                        refresh=False,
                    )

                for issue, sub_issues in zip(batch, results):
                    key = issue_key(issue)
                    if not key:
                        continue
                    normalized = sub_issues or []
                    sub_issue_cache[key] = normalized
                    relationship_count += len(normalized)

                    for sub_issue in normalized:
                        sub_key = issue_key(sub_issue)
                        if (
                            not sub_key
                            or sub_key in queued
                            or not issue_can_have_sub_issues(sub_issue)
                        ):
                            continue
                        queued.add(sub_key)
                        frontier.append(sub_issue)

                if frontier:
                    progress.total += len(frontier)
                    progress.refresh()

            progress.set_postfix(
                current="done",
                relationships=relationship_count,
                refresh=True,
            )


def add_sub_issues_to_grouped_items(
    client: GitHubClient,
    grouped: OrderedDict[str, list[dict[str, Any]]],
    sub_issue_cache: dict[tuple[str, str, int], list[dict[str, Any]]] | None = None,
    workers: int = DEFAULT_WORKERS,
    pass_number: int = 1,
) -> OrderedDict[str, list[dict[str, Any]]]:
    """Insert missing sub-issues after parents while preserving stable order.

    Network queries are prefetched concurrently. The actual tree expansion is
    serial so section order and parent annotations remain deterministic.
    """

    project_keys = project_item_issue_keys(grouped)
    synthetic_keys: set[tuple[str, str, int]] = set()
    parent_title_by_key: dict[tuple[str, str, int], str] = {}
    parent_key_by_key: dict[tuple[str, str, int], tuple[str, str, int]] = {}
    sub_issue_cache = sub_issue_cache if sub_issue_cache is not None else {}

    roots = [
        content
        for items in grouped.values()
        for item in items
        for content in [item.get("content")]
        if isinstance(content, dict)
    ]
    prefetch_sub_issue_tree(
        client,
        roots,
        sub_issue_cache,
        workers,
        pass_number,
    )

    def direct_sub_issue_contents(issue: dict[str, Any]) -> list[dict[str, Any]]:
        key = issue_key(issue)
        return sub_issue_cache.get(key, []) if key else []

    def expand_item(
        item: dict[str, Any],
        ancestors: set[tuple[str, str, int]],
    ) -> list[dict[str, Any]]:
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
            sub_item = synthetic_sub_issue_item(
                sub_issue,
                item,
                parent_title,
                parent_key,
            )
            expanded.extend(expand_item(sub_item, next_ancestors))

        return expanded

    expanded_grouped: OrderedDict[str, list[dict[str, Any]]] = OrderedDict()
    for column, items in grouped.items():
        expanded_items: list[dict[str, Any]] = []
        description = f"Placing sub-issues: {markdown_section_heading(column)}"
        for item in tqdm(items, desc=description, unit="item"):
            expanded_items.extend(expand_item(item, set()))
        expanded_grouped[column] = expanded_items

    expanded_items = [item for items in expanded_grouped.values() for item in items]
    for item in tqdm(expanded_items, desc="Annotating sub-issues", unit="item"):
        key = issue_key_for_item(item)
        if key and key in parent_title_by_key:
            item.setdefault(SUB_ISSUE_PARENT_TITLE_KEY, parent_title_by_key[key])
            if key in parent_key_by_key:
                item.setdefault(SUB_ISSUE_PARENT_KEY_KEY, parent_key_by_key[key])

    ensure_archived_section_at_end(expanded_grouped)
    return expanded_grouped

def expand_issue_graph(
    client: GitHubClient,
    grouped: OrderedDict[str, list[dict[str, Any]]],
    tz: ZoneInfo,
    workers: int = DEFAULT_WORKERS,
    owner_whitelist: frozenset[str] | None = None,
) -> tuple[OrderedDict[str, list[dict[str, Any]]], dict[str, int]]:
    """Expand sub-issues and Markdown references until no new issue remains."""

    attempted_reference_keys: set[tuple[str, str, int]] = set()
    skipped_reference_keys: set[tuple[str, str, int]] = set()
    sub_issue_cache: dict[tuple[str, str, int], list[dict[str, Any]]] = {}
    referenced_added = 0
    reference_failures = 0
    whitelist_skips = 0
    pass_number = 0

    while True:
        pass_number += 1
        before_keys = project_item_issue_keys(grouped)

        grouped = add_sub_issues_to_grouped_items(
            client,
            grouped,
            sub_issue_cache,
            workers,
            pass_number,
        )
        grouped, pass_stats = add_referenced_issues_to_grouped_items(
            client,
            grouped,
            tz,
            attempted_reference_keys,
            pass_number,
            workers,
            owner_whitelist,
            skipped_reference_keys,
        )
        referenced_added += pass_stats["referenced_issue_items_exported"]
        reference_failures += pass_stats["referenced_issue_fetch_failures"]
        whitelist_skips += pass_stats["referenced_issue_whitelist_skips"]

        after_keys = project_item_issue_keys(grouped)
        if after_keys == before_keys:
            break

    return grouped, {
        "referenced_issue_items_exported": referenced_added,
        "referenced_issue_fetch_failures": reference_failures,
        "referenced_issue_whitelist_skips": whitelist_skips,
    }


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
    image_localizer: ImageLocalizer | None = None,
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

        description = f"Markdown: {markdown_section_heading(column)}"
        progress = tqdm(items, desc=description, unit="item")
        for item in progress:
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

            if not is_draft_issue(issue):
                details = issue_repository_details(issue)
                if not details:
                    lines.append("<!-- Skipped timeline: missing repository or issue number in API response. -->")
                    lines.append("")
                    continue

            entries = timeline_entries_for_item(client, item, tz)

            for entry in entries:
                entry_count += 1
                if entry.get("kind") == "comment":
                    comment_count += 1
                else:
                    timeline_event_count += 1

                lines.append(timeline_entry_heading(entry, tz))
                lines.append("")
                body = rendered_timeline_entry_body(entry, tz, parent_anchor_by_key)
                body = link_issue_references(body, issue, parent_anchor_by_key)
                if image_localizer is not None:
                    body = image_localizer.localize_markdown(body, issue)
                lines.append(body)
                lines.append("")

            if image_localizer is not None:
                progress.set_postfix(
                    images=image_localizer.images_downloaded,
                    image_failures=image_localizer.image_download_failures,
                    refresh=False,
                )

    # End files with exactly one newline.
    return "\n".join(lines).rstrip() + "\n", {
        "entries_exported": entry_count,
        "comments_exported": comment_count,
        "timeline_events_exported": timeline_event_count,
        "sub_issue_items_exported": sub_issue_count,
    }




def export_project(
    project_url: str,
    output_path: Path,
    tz_name: str = DEFAULT_TZ,
    workers: int = DEFAULT_WORKERS,
    whitelist: Iterable[str] | None = None,
) -> dict[str, int | str]:
    if not 1 <= workers <= MAX_WORKERS:
        raise ValueError(f"workers must be between 1 and {MAX_WORKERS}")

    owner_whitelist = normalize_owner_whitelist(whitelist)
    output_path = output_path.expanduser()
    print(f"Exporting project: {project_url}", file=sys.stderr)
    parsed_project_url = parse_project_url(project_url)
    print("Getting GitHub token...", file=sys.stderr)
    token = get_github_token(parsed_project_url)

    print("Getting timezone...", file=sys.stderr)
    try:
        tz = ZoneInfo(tz_name)
    except ZoneInfoNotFoundError as exc:
        raise GitHubAPIError(f"unknown timezone: {tz_name}") from exc

    request_spacing = CONCURRENT_REQUEST_SPACING_SECONDS if workers > 1 else 0.0
    print(
        f"Initializing client with {workers} API worker{'s' if workers != 1 else ''}...",
        file=sys.stderr,
    )
    client = GitHubClient(token, request_spacing=request_spacing)

    print("Loading initial project data...", file=sys.stderr)
    project = get_project(client, parsed_project_url)
    view = choose_board_view(project, parsed_project_url.view_number)
    column_field_name = infer_column_field_name(project, view)

    print("Grouping project items...", file=sys.stderr)
    grouped, stats = group_project_items(client, project, column_field_name)

    if owner_whitelist is not None:
        print(
            "Recursive reference whitelist: " + ", ".join(sorted(owner_whitelist)),
            file=sys.stderr,
        )

    print("Loading sub-issues and recursively referenced issues...", file=sys.stderr)
    grouped, expansion_stats = expand_issue_graph(
        client,
        grouped,
        tz,
        workers,
        owner_whitelist,
    )

    output_path.parent.mkdir(parents=True, exist_ok=True)
    image_localizer = ImageLocalizer(client, output_path)

    print("Building Markdown...", file=sys.stderr)
    markdown, markdown_stats = build_markdown(client, grouped, tz, image_localizer)
    image_stats = image_localizer.stats()

    print(f"Writing Markdown to file: {output_path}", file=sys.stderr)
    output_path.write_text(markdown, encoding="utf-8")
    image_localizer.finalize()

    return {
        **stats,
        **expansion_stats,
        **markdown_stats,
        **image_stats,
        "columns_written": len(grouped),
        "project_title": str(project.get("title") or ""),
        "column_field": column_field_name,
        "view_name": str(view.get("name") if view else ""),
        "output_path": str(output_path),
        "workers": workers,
        "recursive_owner_whitelist": ",".join(sorted(owner_whitelist or ())),
    }


def normalize_owner_whitelist(owners: Iterable[str] | None) -> frozenset[str] | None:
    """Normalize optional GitHub account / organization names for matching."""

    if owners is None:
        return None

    normalized: set[str] = set()
    for raw_owner in owners:
        owner = str(raw_owner).strip()
        if owner.startswith("@"):
            owner = owner[1:]
        if not owner or not re.fullmatch(r"[A-Za-z0-9_.-]+", owner):
            raise ValueError(
                f"invalid GitHub account/organization in whitelist: {raw_owner!r}"
            )
        normalized.add(owner.casefold())

    if not normalized:
        raise ValueError("whitelist must contain at least one GitHub account/organization")
    return frozenset(normalized)


def parse_whitelist_account(value: str) -> str:
    try:
        normalized = normalize_owner_whitelist([value])
    except ValueError as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc
    assert normalized is not None
    return next(iter(normalized))


def parse_worker_count(value: str) -> int:
    try:
        workers = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("workers must be an integer") from exc
    if not 1 <= workers <= MAX_WORKERS:
        raise argparse.ArgumentTypeError(
            f"workers must be between 1 and {MAX_WORKERS}"
        )
    return workers


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
    parser.add_argument(
        "-j",
        "--workers",
        type=parse_worker_count,
        default=DEFAULT_WORKERS,
        help=(
            "Concurrent workers for independent issue-history, referenced-issue, "
            "and sub-issue reads (default: 1; try 3 or 4 for a one-off export)."
        ),
    )
    parser.add_argument(
        "--whitelist",
        metavar="ACCOUNT",
        nargs="+",
        action="extend",
        type=parse_whitelist_account,
        help=(
            "Only fetch recursively referenced issues/PRs from repositories owned "
            "by these GitHub accounts or organizations (case-insensitive). Project "
            "cards are always exported. May be repeated."
        ),
    )
    args = parser.parse_args(list(argv))
    if args.whitelist:
        args.whitelist = tuple(dict.fromkeys(args.whitelist))
    return args


def main(argv: Iterable[str] = sys.argv[1:]) -> int:
    args = parse_args(argv)
    output_path = Path(args.output).expanduser()

    try:
        stats = export_project(
            args.project,
            output_path,
            workers=args.workers,
            whitelist=args.whitelist,
        )
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
        f"plus {stats['referenced_issue_items_exported']} recursively referenced issues/PRs "
        f"and {stats['sub_issue_items_exported']} sub-issues "
        f"({stats['archived_issue_or_pr_items']} archived issue/PR cards and "
        f"{stats['archived_draft_items']} archived draft cards) "
        f"across {stats['columns_written']} columns "
        f"to {stats['output_path']}; downloaded {stats['images_downloaded']} images "
        f"and rewrote {stats['image_references_rewritten']} image references",
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

    if int(stats["referenced_issue_fetch_failures"]):
        print(
            f"Could not load {stats['referenced_issue_fetch_failures']} referenced issues/PRs; "
            "their original GitHub links were retained.",
            file=sys.stderr,
        )

    if int(stats["referenced_issue_whitelist_skips"]):
        print(
            f"Skipped {stats['referenced_issue_whitelist_skips']} referenced issues/PRs "
            "outside --whitelist; their original GitHub links were retained.",
            file=sys.stderr,
        )

    if int(stats["image_download_failures"]):
        print(
            f"Could not download {stats['image_download_failures']} embedded images; "
            "their original remote URLs were retained.",
            file=sys.stderr,
        )

    return 0

if __name__ == "__main__":
    raise SystemExit(main())
