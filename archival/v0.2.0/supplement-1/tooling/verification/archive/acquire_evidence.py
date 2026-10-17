"""Explicit network acquisition only; routine PR validation uses committed bytes."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
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
    for name, identity in (("final-code-review-comment.json", 6235925253), ("acceptance-comment.json", 6236142249)):
        value = strict_json(read_bounded(root / name))
        if (value.get("id") != identity
                or value.get("issue_url") != API + "/repos/" + REPOSITORY + "/issues/76"
                or not isinstance(value.get("body"), str) or not value["body"]):
            fail("E_CAPTURE_ID", "Wrong or empty captured final comment: " + name)
    reviews = strict_json(read_bounded(root / "final-review-submissions.json"))
    if not isinstance(reviews, list):
        fail("E_CAPTURE_ID", "Review submissions must preserve the complete paginated list")
    threads = strict_json(read_bounded(root / "review-threads.json"))
    if not isinstance(threads, (dict, list)):
        fail("E_CAPTURE_ID", "Invalid captured review threads")
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
            zip_log = root / "runs" / (str(run_id) + "-logs.zip")
            if log.is_file():
                captured = strict_json(read_bounded(log))
                content = captured.get("logs")
                if content is None and isinstance(captured.get("result"), dict):
                    content = captured["result"].get("structuredContent", {}).get("content")
                if (str(captured.get("job_id")) != str(job["id"])
                        or ("run_id" in captured and captured["run_id"] != run_id)
                        or not isinstance(content, str) or not content.strip()):
                    fail("E_CAPTURE_ID", "Normalized job log is empty or bound to another job/run")
            elif raw_log.is_file():
                if not read_bounded(raw_log):
                    fail("E_CAPTURE_ID", "Raw job log is empty")
            elif not zip_log.is_file():
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
            return payload, {"endpoint": url.split("?", 1)[0], "requested_at": started,
                             "received_at": datetime.now(timezone.utc).isoformat(),
                             "http_status": response.status, "observed_headers": observed}
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
        query = '''query($cursor:String){repository(owner:"HMarcusWH",name:"PermanssonLean"){
pullRequest(number:76){reviewThreads(first:100,after:$cursor){nodes{id isResolved isOutdated path line
comments(first:100){nodes{id databaseId body url author{login}} pageInfo{hasNextPage endCursor}}}
pageInfo{hasNextPage endCursor}}}}}'''
        payload, meta = request("/graphql", body={"query": query, "variables": {"cursor": cursor}})
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
        payload, meta = request(prefix + "/actions/runs/" + str(run["id"]) + "/logs")
        save("runs/" + str(run["id"]) + "-logs.zip", payload, meta)
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
