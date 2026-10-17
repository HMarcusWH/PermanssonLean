"""Explicit network acquisition only; routine PR validation uses committed bytes."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import re
import urllib.parse
import urllib.request

from verification.integrity.reports import HardeningError
from .create_bundle import ACCEPTED, REPOSITORY, R_IDENTITY, R_SOURCE
from .manifest import MAX_METADATA, digest, fail, read_bounded, safe_path, scan_files, stable_json, strict_json

API = "https://api.github.com"
REQUIRED_FILES = {"pr76.json", "final-code-review-comment.json", "acceptance-comment.json",
                  "review-threads.json", "final-review-submissions.json", "R-c10-artifact-metadata.json",
                  "R-c10.zip", "acquisition-index.json"}
FINAL_RUNS = {39045919531: ("Lean", {"build"}),
              39045919534: ("Research Lean", {"research"}),
              39045919547: ("v0.2.0 research release verification", {"research-release"}),
              39045919577: ("Executable verification", {"executable-verification"}),
              39045919601: ("Application contract", {"Application contract (ubuntu-latest)", "Application contract (windows-latest)"})}
# Independently observed PR76 issue-comment REST identities and exact decoded
# UTF-8 bodies, acquired on 2026-10-17. Candidate capture hashes are not their
# authority. The first item is a code-review comment, not mathematical peer
# review or a counted GitHub APPROVED review. No production refresh/override.
FIXED_COMMENTS = {
    "final-code-review-comment.json": {
        "id": 6235925253, "node_id": "IC_kwDOUkBtPs8AAAABc7CrBQ",
        "author": {"id": 199175422, "login": "chatgpt-codex-connector[bot]",
                   "node_id": "BOT_kgDOC98s_g", "type": "Bot"},
        "created_at": "2026-10-17T15:40:46Z", "updated_at": "2026-10-17T15:40:46Z",
        "body_utf8_bytes": 621,
        "body_utf8_sha256": "8d3f62c4f58b93d6254e5caa1278b8784f5e739b04a116c8d95e1865a042ce5e",
    },
    "acceptance-comment.json": {
        "id": 6236142249, "node_id": "IC_kwDOUkBtPs8AAAABc7P6qQ",
        "author": {"id": 173802548, "login": "HMarcusWH",
                   "node_id": "U_kgDOClwENA", "type": "User"},
        "created_at": "2026-10-17T15:54:04Z", "updated_at": "2026-10-17T15:54:04Z",
        "body_utf8_bytes": 3363,
        "body_utf8_sha256": "b33381ce1f8cc769577a192f55107092c4775d0c88f812d6f0ae52031abd36b1",
    },
}


def _index_entries(root):
    value = strict_json(read_bounded(Path(root) / "acquisition-index.json"))
    rows = value.get("entries", value.get("records")) if isinstance(value, dict) else None
    if not isinstance(rows, list) or not rows:
        fail("E_CAPTURE_ID", "Missing truthful acquisition provenance")
    result = {}
    for row in rows:
        if not isinstance(row, dict):
            fail("E_CAPTURE_ID", "Malformed acquisition provenance record")
        path = safe_path(row.get("path"))
        if path in result:
            fail("E_CAPTURE_ID", "Duplicate acquisition record")
        result[path] = row
    return result


def _rest_pages(root, entries, patterns, endpoint, *, normalized=None):
    """Reconstruct bounded exhaustive REST pages with explicit PR76 identity."""
    pages = {}
    for name, entry in entries.items():
        for pattern in patterns:
            match = re.fullmatch(pattern, name)
            if not match:
                continue
            number = int(match.group(1))
            if number < 1 or number > 1000 or number in pages:
                fail("E_CAPTURE_ID", "Duplicate, missing or unbounded capture page number")
            parsed = urllib.parse.urlsplit(entry.get("endpoint", ""))
            try:
                query = urllib.parse.parse_qs(parsed.query, strict_parsing=True)
            except ValueError:
                fail("E_CAPTURE_ID", "Malformed captured pagination query")
            if (parsed.scheme != "https" or parsed.netloc != "api.github.com"
                    or parsed.path != endpoint or parsed.fragment
                    or query.get("page") != [str(number)] or query.get("per_page") != ["100"]
                    or set(query) != {"page", "per_page"}
                    or entry.get("representation") not in {"raw_http", "raw_http_response_body", "normalized_connector_json"}):
                fail("E_CAPTURE_ID", "REST pagination identity/request does not match PR76")
            if entry.get("representation") == "normalized_connector_json":
                expected_scope = {"repo_full_name": REPOSITORY, "pr_number": 76, "page": number, "per_page": 100}
                if (entry.get("endpoint_role") != "resource_identity_only"
                        or entry.get("request") != expected_scope):
                    fail("E_CAPTURE_ID", "Normalized REST connector page lacks its exact request scope")
            rows = strict_json(read_bounded(Path(root) / name))
            if not isinstance(rows, list) or len(rows) > 100:
                fail("E_CAPTURE_ID", "Malformed or oversized captured REST page")
            pages[number] = rows
    if not pages or sorted(pages) != list(range(1, len(pages) + 1)):
        fail("E_CAPTURE_ID", "Captured REST pages are missing or not contiguous from page one")
    values = []
    exhausted = False
    for number in sorted(pages):
        rows = pages[number]
        if exhausted and rows:
            fail("E_CAPTURE_ID", "Nonempty REST page follows a terminal short page")
        if len(rows) < 100:
            exhausted = True
        values.extend(rows)
    if not exhausted:
        fail("E_CAPTURE_ID", "Captured REST pagination has no terminal page")
    if normalized is not None and normalized != values:
        fail("E_CAPTURE_ID", "Normalized review submissions differ from captured REST pages")
    return values, len(pages)


def _connector_threads(page):
    if (not isinstance(page, dict)
            or page.get("request") != {"tool": "mcp__codex_apps__github_list_pull_request_review_threads",
                                      "repo_full_name": REPOSITORY, "pr_number": 76}
            or page.get("pagination_state") != "NOT_EXPOSED"):
        fail("E_CAPTURE_ID", "Connector review-thread capture lacks its exact PR76 request/boundary")
    result = page.get("result")
    if not isinstance(result, dict) or result.get("isError") is not False:
        fail("E_CAPTURE_ID", "Original connector response is missing or not an explicit successful result")
    structured = result.get("structuredContent")
    if not isinstance(structured, dict) or not isinstance(structured.get("review_threads"), list):
        fail("E_CAPTURE_ID", "Original connector response lacks review thread nodes")
    return structured["review_threads"]


def _utc_timestamp(value, message):
    """Validate UTC capture timestamps, retaining their exact original text."""
    if (not isinstance(value, str)
            or not re.fullmatch(r"[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}(?:\.[0-9]+)?Z", value)):
        fail("E_CAPTURE_ID", message)
    try:
        return datetime.fromisoformat(value[:-1] + "+00:00")
    except ValueError:
        fail("E_CAPTURE_ID", message)


def validate_review_capture(root, entries, pr, reviews, threads):
    reviews, page_count = _rest_pages(root, entries,
        [r"review-pages/([1-9][0-9]*)\.json", r"pagination/reviews-([1-9][0-9]*)\.json"],
        "/repos/" + REPOSITORY + "/pulls/76/reviews", normalized=reviews)
    normalized_entry = entries.get("final-review-submissions.json", {})
    if "pages" in normalized_entry and normalized_entry["pages"] != page_count:
        fail("E_CAPTURE_ID", "Normalized review page count differs from captured pagination")
    identities = set()
    for row in reviews:
        if (not isinstance(row, dict) or type(row.get("id")) is not int or row["id"] <= 0
                or row["id"] in identities
                or row.get("pull_request_url") != API + "/repos/" + REPOSITORY + "/pulls/76"
                or row.get("html_url") != "https://github.com/" + REPOSITORY + "/pull/76#pullrequestreview-" + str(row["id"])):
            fail("E_CAPTURE_ID", "Captured review identity belongs to another PR or is duplicate")
        identities.add(row["id"])
    normalized_threads = threads.get("review_threads") if isinstance(threads, dict) else threads
    if not isinstance(normalized_threads, list):
        fail("E_CAPTURE_ID", "Normalized review-thread collection is malformed")
    sources = [name for name in entries if re.fullmatch(r"thread-pages/([1-9][0-9]*)\.json", name)]
    if sources:
        # The connector's complete-list interface does not expose GraphQL
        # cursors. Preserve that limit and obtain collection completeness from
        # the separately exhausted REST inline-comment pages below.
        if (sources != ["thread-pages/1.json"]
                or any(re.fullmatch(r"pagination/threads-([1-9][0-9]*)\.json", name) for name in entries)):
            fail("E_CAPTURE_ID", "Unsupported connector review-thread pagination")
        source_page = strict_json(read_bounded(Path(root) / sources[0]))
        source_record = entries[sources[0]]
        if (source_record.get("endpoint") != API + "/repos/" + REPOSITORY + "/pulls/76"
                or source_record.get("endpoint_role") != "resource_identity_only"
                or source_record.get("representation") != "normalized_connector_capture"
                or source_record.get("request") != source_page.get("request")
                or source_record.get("pagination_state") != "NOT_EXPOSED"):
            fail("E_CAPTURE_ID", "Connector source provenance disagrees with actual captured request")
        captured = _connector_threads(source_page)
    else:
        captured = _graphql_thread_pages(root, entries)
    if normalized_threads != captured:
        fail("E_CAPTURE_ID", "Normalized review threads differ from original captured response")
    comments, _ = _rest_pages(root, entries, [r"thread-comment-pages/([1-9][0-9]*)\.json"],
                              "/repos/" + REPOSITORY + "/pulls/76/comments")
    by_id = {}
    for row in comments:
        if (not isinstance(row, dict) or type(row.get("id")) is not int or row["id"] <= 0
                or row["id"] in by_id
                or type(row.get("pull_request_review_id")) is not int
                or row["pull_request_review_id"] not in identities
                or row.get("pull_request_url") != API + "/repos/" + REPOSITORY + "/pulls/76"
                or row.get("html_url") != "https://github.com/" + REPOSITORY + "/pull/76#discussion_r" + str(row["id"])
                or not isinstance(row.get("body"), str)):
            fail("E_CAPTURE_ID", "REST inline comment has the wrong PR/review identity or duplicate ID")
        for field in ("created_at", "updated_at"):
            _utc_timestamp(row.get(field), "REST inline comment lacks a valid " + field + " timestamp")
        by_id[row["id"]] = row
    if type(pr.get("review_comments")) is not int or pr["review_comments"] != len(by_id):
        fail("E_CAPTURE_ID", "Captured PR inline-comment count differs from exhaustive REST pages")
    seen_threads, seen_comments = set(), set()
    for thread in captured:
        if (not isinstance(thread, dict) or not isinstance(thread.get("id"), str)
                or thread["id"] in seen_threads):
            fail("E_CAPTURE_ID", "Duplicate or malformed review-thread identity")
        seen_threads.add(thread["id"])
        thread_comments = thread.get("comments")
        if isinstance(thread_comments, dict):
            thread_comments = thread_comments.get("nodes")
        if not isinstance(thread_comments, list) or not thread_comments:
            fail("E_CAPTURE_ID", "Review-thread comment collection is incomplete")
        for comment in thread_comments:
            identity = comment.get("database_id", comment.get("databaseId"))
            original = by_id.get(identity)
            if identity in seen_comments or original is None or comment.get("body") != original["body"]:
                fail("E_CAPTURE_ID", "Thread comment ID/body differs from exhaustive REST capture")
            for field, graphql in (("created_at", "createdAt"), ("updated_at", "updatedAt")):
                values = [comment[key] for key in (field, graphql) if key in comment]
                if not values or any(value != original[field] for value in values):
                    fail("E_CAPTURE_ID", "Thread comment timestamp is missing or differs from REST capture")
            seen_comments.add(identity)
    if seen_comments != set(by_id):
        fail("E_CAPTURE_ID", "Review threads omit captured inline comments")


def _graphql_thread_pages(root, entries):
    pages = {}
    for name in entries:
        match = re.fullmatch(r"pagination/threads-([1-9][0-9]*)\.json", name)
        if match:
            pages[int(match.group(1))] = name
    if not pages or sorted(pages) != list(range(1, len(pages) + 1)):
        fail("E_CAPTURE_ID", "Original review-thread source pages are missing")
    result, cursor = [], None
    for number in sorted(pages):
        record = entries[pages[number]]
        request = record.get("request", {})
        variables = request.get("variables", {})
        if (record.get("endpoint") != API + "/graphql"
                or variables != {"owner": "HMarcusWH", "name": "PermanssonLean", "number": 76, "cursor": cursor}):
            fail("E_CAPTURE_ID", "GraphQL thread request/cursor is not bound to PR76")
        value = strict_json(read_bounded(Path(root) / pages[number]))
        try:
            repository = value["data"]["repository"]
            pr = repository["pullRequest"]
            connection = pr["reviewThreads"]
            nodes, page_info = connection["nodes"], connection["pageInfo"]
        except (KeyError, TypeError):
            fail("E_CAPTURE_ID", "Malformed GraphQL thread response")
        if (value.get("errors") or repository.get("nameWithOwner") != REPOSITORY or pr.get("number") != 76
                or not isinstance(nodes, list) or len(nodes) > 100
                or page_info.get("hasNextPage") is not (number < len(pages))):
            fail("E_CAPTURE_ID", "GraphQL thread identity or terminal pagination differs")
        for thread in nodes:
            if thread.get("comments", {}).get("pageInfo", {}).get("hasNextPage") is not False:
                fail("E_CAPTURE_ID", "GraphQL thread comment pagination is incomplete")
        cursor = page_info.get("endCursor")
        if number < len(pages) and not isinstance(cursor, str):
            fail("E_CAPTURE_ID", "GraphQL continuation cursor is missing")
        result.extend(nodes)
    return result


def validate_r_identity(metadata):
    if not isinstance(metadata, dict):
        fail("E_CAPTURE_ID", "Artifact metadata is not an object")
    workflow = metadata.get("workflow_run", {})
    if (metadata.get("id") != R_IDENTITY["artifact_id"]
            or metadata.get("size_in_bytes") != R_IDENTITY["size"]
            or metadata.get("digest") != "sha256:" + R_IDENTITY["sha256"]
            or workflow.get("id") != R_IDENTITY["run_id"]
            or workflow.get("head_sha") != R_SOURCE["head_sha"]
            or ("url" in metadata and metadata["url"] != API + "/repos/" + REPOSITORY + "/actions/artifacts/12106535829")
            or ("archive_download_url" in metadata and metadata["archive_download_url"] != API + "/repos/" + REPOSITORY + "/actions/artifacts/12106535829/zip")
            or ("repository_id" in workflow and workflow["repository_id"] != 1379953982)):
        fail("E_CAPTURE_ID", "Historical R artifact/run/head/size/digest identity differs")


def validate_r_bytes(raw):
    if len(raw) != R_IDENTITY["size"] or digest(raw) != R_IDENTITY["sha256"]:
        fail("E_EVIDENCE_HASH", "Original R publisher bytes differ from the fixed external identity")


def _validate_job_log_text(content):
    if not isinstance(content, str) or "\0" in content:
        fail("E_CAPTURE_ID", "Job log is not nonempty timestamped GitHub log text")
    try:
        content.encode("utf-8")
    except UnicodeError:
        fail("E_CAPTURE_ID", "Job log is not valid UTF-8 text")
    match = re.match(r"\ufeff?([0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}(?:\.[0-9]+)?Z)[ \t]\S", content)
    if match is None:
        fail("E_CAPTURE_ID", "Job log is not nonempty timestamped GitHub log text")
    _utc_timestamp(match.group(1), "Job log has an invalid calendar timestamp")


def _validate_fixed_comment(value, name):
    expected = FIXED_COMMENTS[name]
    identity = expected["id"]
    author = value.get("user") if isinstance(value, dict) else None
    if (not isinstance(value, dict) or type(value.get("id")) is not int
            or value["id"] != identity or value.get("node_id") != expected["node_id"]
            or value.get("url") != API + "/repos/" + REPOSITORY + "/issues/comments/" + str(identity)
            or value.get("issue_url") != API + "/repos/" + REPOSITORY + "/issues/76"
            or value.get("html_url") != "https://github.com/" + REPOSITORY + "/pull/76#issuecomment-" + str(identity)
            or not isinstance(author, dict) or type(author.get("id")) is not int
            or any(author.get(key) != pinned for key, pinned in expected["author"].items())
            or any(value.get(key) != expected[key] for key in ("created_at", "updated_at"))
            or not isinstance(value.get("body"), str)):
        fail("E_CAPTURE_ID", "Fixed historical comment identity/author/timestamps differ: " + name)
    try:
        body = value["body"].encode("utf-8")
    except UnicodeError:
        fail("E_CAPTURE_ID", "Fixed historical comment body is not valid UTF-8: " + name)
    if len(body) != expected["body_utf8_bytes"] or digest(body) != expected["body_utf8_sha256"]:
        fail("E_CAPTURE_ID", "Fixed historical comment body differs: " + name)


def validate_evidence(root):
    root = Path(root)
    scan_files(root)  # Reject symlinks/types before reading or copying evidence.
    missing = REQUIRED_FILES - {p.name for p in root.iterdir() if p.is_file()}
    if missing:
        fail("E_CAPTURE_ID", "Required final R capture or code-review evidence is missing: " + ", ".join(sorted(missing)))
    metadata = strict_json(read_bounded(root / "R-c10-artifact-metadata.json"))
    validate_r_identity(metadata)
    raw = read_bounded(root / "R-c10.zip", R_IDENTITY["size"])
    validate_r_bytes(raw)
    pr = strict_json(read_bounded(root / "pr76.json"))
    if (pr.get("number") != 76 or pr.get("head", {}).get("sha") != R_SOURCE["head_sha"]
            or pr.get("base", {}).get("sha") != R_SOURCE["base_sha"]
            or pr.get("merge_commit_sha") != ACCEPTED
            or pr.get("base", {}).get("repo", {}).get("full_name") != REPOSITORY):
        fail("E_CAPTURE_ID", "Final PR capture has the wrong repository or H/B/M")
    entries_by_path = _index_entries(root)
    for name, expected in FIXED_COMMENTS.items():
        value = strict_json(read_bounded(root / name))
        _validate_fixed_comment(value, name)
        if entries_by_path.get(name, {}).get("endpoint") != API + "/repos/" + REPOSITORY + "/issues/comments/" + str(expected["id"]):
            fail("E_CAPTURE_ID", "Fixed historical comment acquisition endpoint differs: " + name)
    reviews = strict_json(read_bounded(root / "final-review-submissions.json"))
    if not isinstance(reviews, list):
        fail("E_CAPTURE_ID", "Review submissions must preserve the complete paginated list")
    threads = strict_json(read_bounded(root / "review-threads.json"))
    if not isinstance(threads, (dict, list)):
        fail("E_CAPTURE_ID", "Invalid captured review threads")
    validate_review_capture(root, entries_by_path, pr, reviews, threads)
    for run_id, (name, expected_jobs) in FINAL_RUNS.items():
        run_path = root / "runs" / (str(run_id) + ".json")
        jobs_path = root / "runs" / (str(run_id) + "-jobs.json")
        if not run_path.is_file() or not jobs_path.is_file():
            fail("E_CAPTURE_ID", "Missing one of the five final workflow/job captures")
        run = strict_json(read_bounded(run_path))
        if (run.get("id") != run_id or run.get("name") != name
                or run.get("conclusion") != "success" or run.get("status") != "completed"
                or run.get("event") != "pull_request" or run.get("head_sha") != R_SOURCE["head_sha"]
                or run.get("repository", {}).get("full_name") != REPOSITORY):
            fail("E_CAPTURE_ID", "Final R workflow is not the successful source-bound PR run")
        jobs = strict_json(read_bounded(jobs_path))
        rows = jobs.get("jobs") if isinstance(jobs, dict) else None
        if (not isinstance(rows, list) or jobs.get("total_count") != len(rows)
                or {row.get("name") for row in rows} != expected_jobs or len(rows) != len(expected_jobs)):
            fail("E_CAPTURE_ID", "Final R job inventory is missing, duplicate or incomplete")
        for job in rows:
            if (job.get("run_id") != run_id or job.get("head_sha") != R_SOURCE["head_sha"]
                    or job.get("conclusion") != "success" or job.get("status") != "completed"):
                fail("E_CAPTURE_ID", "Final job has the wrong source, run or result")
            log = root / "runs" / ("job-" + str(job.get("id")) + "-logs.json")
            raw_log = root / "runs" / ("job-" + str(job.get("id")) + "-logs.txt")
            selected_log = log if log.is_file() else raw_log
            log_entry = entries_by_path.get(selected_log.relative_to(root).as_posix(), {})
            if log_entry.get("endpoint") != API + "/repos/" + REPOSITORY + "/actions/jobs/" + str(job["id"]) + "/logs":
                fail("E_CAPTURE_ID", "Job-log acquisition endpoint is missing or bound to another job")
            if log.is_file():
                captured = strict_json(read_bounded(log))
                content = captured.get("logs")
                if content is None and isinstance(captured.get("result"), dict):
                    content = captured["result"].get("structuredContent", {}).get("content")
                if (str(captured.get("job_id")) != str(job["id"])
                        or ("run_id" in captured and captured["run_id"] != run_id)
                        or not isinstance(content, str) or not content.strip()):
                    fail("E_CAPTURE_ID", "Normalized job log is empty or bound to another job/run")
                _validate_job_log_text(content)
            elif raw_log.is_file():
                try:
                    content = read_bounded(raw_log).decode("utf-8")
                except UnicodeError:
                    fail("E_CAPTURE_ID", "Raw job log is not valid UTF-8 text")
                _validate_job_log_text(content)
            else:
                fail("E_CAPTURE_ID", "Missing final job log capture")
    index = strict_json(read_bounded(root / "acquisition-index.json"))
    entries = index.get("entries", index.get("records")) if isinstance(index, dict) else None
    if not isinstance(entries, list) or not entries:
        fail("E_CAPTURE_ID", "Missing truthful acquisition provenance")
    seen = set()
    for row in entries:
        path = safe_path(row.get("path"))
        if path in seen or path == "acquisition-index.json":
            fail("E_CAPTURE_ID", "Duplicate/self-referential acquisition entry")
        seen.add(path)
        payload = read_bounded(root / path)
        if row.get("sha256") != digest(payload) or row.get("size") != len(payload):
            fail("E_EVIDENCE_HASH", "Acquisition index payload digest differs: " + path)
        representation = row.get("representation")
        allowed = {"raw_http", "normalized_connector", "raw_http_response_body",
                   "assembled_paginated_api_json", "original_publisher_zip_via_GitHub_connector",
                   "normalized_connector_response", "normalized_connector_json", "normalized_connector_text",
                   "decoded_base64_connector_response", "normalized_connector_capture"}
        if representation not in allowed:
            fail("E_CAPTURE_ID", "Unknown acquisition representation")
        if representation == "assembled_paginated_api_json":
            if type(row.get("pages")) is not int or row["pages"] <= 0:
                fail("E_CAPTURE_ID", "Assembled pagination lacks its page provenance")
            continue
        endpoint = row.get("endpoint", "")
        parsed = urllib.parse.urlsplit(endpoint)
        if (parsed.scheme != "https" or parsed.netloc != "api.github.com"
                or parsed.username or parsed.password
                or any(word in parsed.query.lower() for word in ("token=", "signature=", "credential="))):
            fail("E_CAPTURE_ID", "Unsafe or undocumented acquisition provenance")
        observed_time = row.get("requested_at", row.get("acquired_at", row.get("acquired_on")))
        if observed_time is None and representation == "normalized_connector":
            captured = strict_json(payload)
            if isinstance(captured, dict):
                observed_time = captured.get("acquired_at")
        if not isinstance(observed_time, str):
            fail("E_CAPTURE_ID", "No observed acquisition date/time")
        try:
            datetime.fromisoformat(observed_time.replace(" UTC", "+00:00").replace("Z", "+00:00"))
        except ValueError:
            fail("E_CAPTURE_ID", "Invalid observed acquisition time")
    actual = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()}
    if seen != actual - {"acquisition-index.json"}:
        fail("E_CAPTURE_ID", "Acquisition index omits or invents captured payloads")
    return {"original_artifact_sha256": digest(raw), "artifact_bytes": len(raw),
            "run_id": R_IDENTITY["run_id"], "capture_files": len(seen),
            "publisher_authentication": "not_created_by_offline_checksums"}


class SafeRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, fp, code, msg, headers, newurl):
        if urllib.parse.urlsplit(newurl).scheme != "https":
            fail("E_CAPTURE_ID", "Evidence redirects must remain HTTPS")
        result = super().redirect_request(request, fp, code, msg, headers, newurl)
        if result is not None and urllib.parse.urlsplit(newurl).netloc != "api.github.com":
            result.remove_header("Authorization")
        return result


def acquire(output):
    """Acquire exact captures with an explicitly supplied read-authorized token.

    Token scope is an operator prerequisite, never expanded by this command.
    No redirect URL or credential is written into acquisition metadata.
    """
    output = Path(output)
    if output.exists() or output.is_symlink():
        fail("E_CAPTURE_ID", "Acquisition output must be new", 2)
    token = os.environ.get("GH_TOKEN")
    if not token:
        fail("E_AUTHORIZATION_MISSING", "Supply a read-authorized GH_TOKEN for acquisition", 3)
    output.mkdir(parents=True)
    index = []
    opener = urllib.request.build_opener(SafeRedirect())
    def request(endpoint, *, body=None):
        url = API + endpoint
        headers = {"Accept": "application/vnd.github+json", "Authorization": "Bearer " + token,
                   "X-GitHub-Api-Version": "2022-11-28", "User-Agent": "Permansson-hardening-acquisition"}
        started = datetime.now(timezone.utc).isoformat()
        req = urllib.request.Request(url, headers=headers, data=stable_json(body) if body else None)
        with opener.open(req, timeout=60) as response:
            payload = response.read(MAX_METADATA + 1)
            if len(payload) > MAX_METADATA:
                fail("E_LIMIT", "Acquired capture exceeds metadata budget")
            observed = {key: response.headers[key] for key in ("ETag", "Date", "X-GitHub-Api-Version-Selected") if key in response.headers}
            return payload, {"endpoint": url, "requested_at": started,
                             "received_at": datetime.now(timezone.utc).isoformat(),
                             "http_status": response.status, "observed_headers": observed,
                             **({"request": body} if body else {})}
    def save(path, data, meta, representation="raw_http"):
        target = output / safe_path(path)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        index.append({**meta, "path": path, "size": len(data), "sha256": digest(data), "representation": representation})
    prefix = "/repos/" + REPOSITORY
    captures = {"pr76.json": prefix + "/pulls/76",
                "final-code-review-comment.json": prefix + "/issues/comments/6235925253",
                "acceptance-comment.json": prefix + "/issues/comments/6236142249",
                "R-c10-artifact-metadata.json": prefix + "/actions/artifacts/12106535829",
                "R-c10.zip": prefix + "/actions/artifacts/12106535829/zip"}
    for path, endpoint in captures.items():
        payload, meta = request(endpoint)
        save(path, payload, meta)
    reviews = []
    for page in range(1, 1001):
        payload, meta = request(prefix + f"/pulls/76/reviews?per_page=100&page={page}")
        rows = strict_json(payload)
        if not isinstance(rows, list):
            fail("E_CAPTURE_ID", "Paginated reviews response is not a list")
        reviews.extend(rows)
        save(f"pagination/reviews-{page}.json", payload, meta)
        if len(rows) < 100:
            break
    else:
        fail("E_LIMIT", "Review pagination exceeded safety bound")
    save("final-review-submissions.json", stable_json(reviews),
         {"endpoint": API + prefix + "/pulls/76/reviews", "requested_at": meta["requested_at"],
          "derivation": "combined_complete_pagination"}, "normalized_connector")
    threads, cursor = [], None
    for page in range(1, 1001):
        query = '''query($owner:String!,$name:String!,$number:Int!,$cursor:String){repository(owner:$owner,name:$name){nameWithOwner
pullRequest(number:$number){number reviewThreads(first:100,after:$cursor){nodes{id isResolved isOutdated path line
comments(first:100){nodes{id databaseId body url createdAt updatedAt author{login}} pageInfo{hasNextPage endCursor}}}
pageInfo{hasNextPage endCursor}}}}}'''
        payload, meta = request("/graphql", body={"query": query, "variables": {
            "owner": "HMarcusWH", "name": "PermanssonLean", "number": 76, "cursor": cursor}})
        value = strict_json(payload)
        if value.get("errors"):
            fail("E_CAPTURE_ID", "GraphQL review-thread acquisition failed")
        result = value["data"]["repository"]["pullRequest"]["reviewThreads"]
        for thread in result["nodes"]:
            if thread["comments"]["pageInfo"]["hasNextPage"]:
                fail("E_CAPTURE_ID", "A review thread needs additional comment pagination; capture manually", 3)
        threads.extend(result["nodes"])
        save(f"pagination/threads-{page}.json", payload, meta)
        if not result["pageInfo"]["hasNextPage"]:
            break
        cursor = result["pageInfo"]["endCursor"]
    else:
        fail("E_LIMIT", "Thread pagination exceeded safety bound")
    save("review-threads.json", stable_json(threads),
         {"endpoint": API + "/graphql", "requested_at": meta["requested_at"], "derivation": "combined_complete_pagination"},
         "normalized_connector")
    for page in range(1, 1001):
        payload, meta = request(prefix + f"/pulls/76/comments?per_page=100&page={page}")
        comments = strict_json(payload)
        if not isinstance(comments, list):
            fail("E_CAPTURE_ID", "Inline-comment pagination is not a list")
        save(f"thread-comment-pages/{page}.json", payload, meta)
        if len(comments) < 100:
            break
    else:
        fail("E_LIMIT", "Inline-comment pagination exceeded safety bound")
    pr = strict_json(read_bounded(output / "pr76.json"))
    payload, meta = request(prefix + "/actions/runs?event=pull_request&head_sha=" + pr["head"]["sha"] + "&per_page=100")
    runs = strict_json(payload)["workflow_runs"]
    save("runs/final-runs.json", payload, meta)
    runs_by_id = {run["id"]: run for run in runs}
    if not set(FINAL_RUNS) <= set(runs_by_id):
        fail("E_CAPTURE_ID", "Required original final workflow IDs are unavailable", 3)
    for run_id in FINAL_RUNS:
        run = runs_by_id[run_id]
        payload, meta = request(prefix + "/actions/runs/" + str(run["id"]))
        save("runs/" + str(run["id"]) + ".json", payload, meta)
        payload, meta = request(prefix + "/actions/runs/" + str(run["id"]) + "/jobs?per_page=100")
        jobs = strict_json(payload)
        if jobs.get("total_count", 0) > 100:
            fail("E_CAPTURE_ID", "Job pagination requires manual complete capture", 3)
        save("runs/" + str(run["id"]) + "-jobs.json", payload, meta)
        for job in jobs["jobs"]:
            payload, meta = request(prefix + "/actions/jobs/" + str(job["id"]) + "/logs")
            save("runs/job-" + str(job["id"]) + "-logs.txt", payload, meta)
    (output / "acquisition-index.json").write_bytes(stable_json({"format": "Permansson.Hardening.Acquisition.v1", "entries": index}))
    return validate_evidence(output)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True)
    args = parser.parse_args(argv)
    try:
        result = acquire(args.output)
        print("Original R capture verified: " + result["original_artifact_sha256"])
        return 0
    except HardeningError as exc:
        print(exc.code + ": " + str(exc))
        return exc.exit_code


if __name__ == "__main__":
    raise SystemExit(main())
