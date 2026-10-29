"""Read-only, exact-H delivery of authentic T/T2 and A2 GitHub ZIPs.

This is a transportation component, NOT a reviewer decision. The actual
required-check job supplies the true PR event identity. A separately
authorized security review ID is a runtime input, never committed source.

The independent consumer *again* runs infrastructure_acceptance's exact
run/job/check/artifact and source/semantic verifiers. This module cannot mark
a failed original producer, changed historical source or unreviewed execution
as approved. It never runs a remote workflow or modifies GitHub.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import urllib.parse
import urllib.request

from final_closure_authenticate import live as real_live
from infrastructure_acceptance_v2 import (
    FORMAT as EVIDENCE_FORMAT, EXPECTED_ARTIFACTS, ACTIVE_WORKFLOW,
    authenticate_original_zip, inspect_zip, inspect_T, inspect_A2,
    verify_A2_dependency_bridge,
)
from release_target import (
    B113, REPOSITORY, BINDING_FORMAT, SHA as SHA40,
)
from pr113_required_dual_gate_v2 import actual_ci_event
from pr113_historical_evidence_contract_v2 import validate_envelope

ROOT = Path(__file__).resolve().parents[2]
FORMAT = "Permansson.PR113.ExactHistoricalArtifactDelivery.v2"
MAX_ARTIFACT = 256 * 1024 * 1024
MAX_PAGE = 100
MAX_DOWNLOAD_REDIRECTS = 5


class DeliveryError(ValueError):
    pass


def need(ok, msg):
    if not ok:
        raise DeliveryError(msg)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def approved_https_url(url):
    """Permit only HTTPS GitHub API and signed GitHub artifact CDN endpoints."""
    try:
        parts = urllib.parse.urlsplit(url)
        host = (parts.hostname or "").lower()
        return (parts.scheme == "https" and parts.port in (None, 443)
                and parts.username is None and parts.password is None
                and (host == "api.github.com"
                     or host.endswith(".githubusercontent.com")
                     or host.endswith(".blob.core.windows.net")))
    except ValueError:
        return False


class BoundedGithubRedirect(urllib.request.HTTPRedirectHandler):
    def __init__(self):
        self.hops = 0

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        self.hops += 1
        if self.hops > MAX_DOWNLOAD_REDIRECTS or not approved_https_url(newurl):
            raise DeliveryError("historical artifact redirect left the approved HTTPS source")
        child = super().redirect_request(req, fp, code, msg, headers, newurl)
        need(child is not None, "historical artifact redirect unavailable")
        # Never forward the GitHub Actions bearer token to the signed CDN.
        if urllib.parse.urlsplit(newurl).hostname != "api.github.com":
            for k in list(child.headers):
                if k.lower() == "authorization":
                    del child.headers[k]
            for k in list(child.unredirected_hdrs):
                if k.lower() == "authorization":
                    del child.unredirected_hdrs[k]
        return child


def github_artifact_bytes(artifact_id, *, token=None):
    """Download bounded original GitHub-created ZIP bytes without extraction."""
    need(type(artifact_id) is int and artifact_id > 0,
         "unsigned GitHub artifact ID")
    if token is None:
        token = os.environ.get("GITHUB_TOKEN")
    need(isinstance(token, str) and bool(token),
         "read-only GitHub Actions token required for original artifact")
    url = ("https://api.github.com/repos/" + REPOSITORY
           + "/actions/artifacts/" + str(artifact_id) + "/zip")
    need(approved_https_url(url), "GitHub artifact source not trusted")
    request = urllib.request.Request(url, headers={
        "Accept": "application/vnd.github+json",
        "User-Agent": "Permansson-PR113-Historical-ReadOnly/1",
        "Authorization": "Bearer " + token,
    })
    try:
        client = urllib.request.build_opener(BoundedGithubRedirect())
        with client.open(request, timeout=55) as resp:
            size = resp.headers.get("Content-Length")
            if size is not None:
                need(int(size) <= MAX_ARTIFACT,
                     "GitHub artifact exceeds original ZIP budget")
            data = resp.read(MAX_ARTIFACT + 1)
    except (OSError, ValueError, urllib.error.URLError) as exc:
        raise DeliveryError("authentic GitHub artifact download unavailable") from exc
    need(0 < len(data) <= MAX_ARTIFACT and data.startswith(b"PK"),
         "original GitHub ZIP empty, unbounded or replaced")
    return data


def unique_job_and_artifact(run, jobs_data, artifacts_data, *, kind, head):
    need(kind in EXPECTED_ARTIFACTS, "unknown historical producing leg")
    job_name, artifact_name = EXPECTED_ARTIFACTS[kind]
    jobs = jobs_data.get("jobs") if isinstance(jobs_data, dict) else None
    artifacts = (artifacts_data.get("artifacts")
                 if isinstance(artifacts_data, dict) else None)
    need(isinstance(jobs, list) and len(jobs) < MAX_PAGE and
         isinstance(artifacts, list) and len(artifacts) < MAX_PAGE,
         "historical producer job/artifact inventory truncated or malformed")
    need(isinstance(run, dict) and run.get("head_sha") == head and
         run.get("head_branch") == "research/final-mathematical-closure" and
         run.get("event") == "push" and
         run.get("status") == "completed" and
         run.get("conclusion") == "success" and
         str(run.get("path", "")).endswith(ACTIVE_WORKFLOW) and
         type(run.get("run_attempt")) is int and run["run_attempt"] > 0,
         "historical producing run not successful exact-H source")
    j = [x for x in jobs if isinstance(x, dict) and x.get("name") == job_name]
    a = [x for x in artifacts if isinstance(x, dict)
         and x.get("name") == artifact_name]
    need(len(j) == 1 and len(a) == 1,
         "missing or ambiguous historical original job/artifact")
    job, artifact = j[0], a[0]
    need(job.get("run_id") == run.get("id") and
         job.get("run_attempt") == run["run_attempt"] and
         job.get("head_sha") == head and
         job.get("status") == "completed" and
         job.get("conclusion") == "success" and
         type(job.get("id")) is int and job["id"] > 0 and
         type(artifact.get("id")) is int and artifact["id"] > 0 and
         artifact.get("expired") is False and
         (artifact.get("workflow_run") or {}).get("id") == run.get("id") and
         (artifact.get("workflow_run") or {}).get("head_sha") == head,
         "historical original artifact did not originate from successful job")
    url = job.get("check_run_url")
    need(isinstance(url, str) and
         re.fullmatch(r"https://api.github.com/repos/" +
                      re.escape(REPOSITORY) + r"/check-runs/[1-9][0-9]*", url),
         "historical original check URL is not an authentic GitHub API check")
    cid = int(url.rsplit("/", 1)[-1])
    return {
        "run_id": run["id"], "run_attempt": run["run_attempt"],
        "job_id": job["id"], "check_run_id": cid,
        "artifact_id": artifact["id"],
    }


def collect(head, run_id, *, live=real_live, download=github_artifact_bytes,
            committed_manifest=None):
    """Return two immutable archive bytes and a non-approved provenance record."""
    need(isinstance(head, str) and SHA40.fullmatch(head),
         "actual PR source H required")
    need(type(run_id) is int and run_id > 0, "original producer run ID required")
    run = live("/actions/runs/" + str(run_id))
    jobs = live("/actions/runs/" + str(run_id) + "/jobs?per_page=100")
    artifacts = live("/actions/runs/" + str(run_id) + "/artifacts?per_page=100")
    selected, data, details = {}, {}, {}
    for kind in ("T", "A2"):
        source = unique_job_and_artifact(
            run, jobs, artifacts, kind=kind, head=head)
        raw = download(source["artifact_id"])
        # Re-execute the independent original provenance validator, which
        # authenticates live check-run, timestamps, ZIP SHA and source H.
        source_receipt = authenticate_original_zip(
            kind, source, raw, head, live=live)
        members = inspect_zip(raw)
        if kind == "T":
            scope = inspect_T(members, head)
        else:
            scope = inspect_A2(members, head)
            need(type(committed_manifest) is bytes
                 and 0 < len(committed_manifest) <= 1024*1024,
                 "current-H committed Lake manifest required")
            scope["dependency_bridge_sha256"] = verify_A2_dependency_bridge(
                members, head, manifest_raw=committed_manifest)
        selected[kind], data[kind], details[kind] = source, raw, {
            "source": source_receipt,
            "scope": scope, "archive_sha256": sha(raw),
        }
    need(selected["T"]["run_id"] == selected["A2"]["run_id"]
         and selected["T"]["job_id"] != selected["A2"]["job_id"]
         and selected["T"]["artifact_id"] != selected["A2"]["artifact_id"],
         "two genuine historical legs must be distinct within one exact-H run")
    return data, selected, details


def detached_target(context):
    from release_target import candidate_bindings
    need(isinstance(context, dict), "real PR context missing")
    record = {
        "format": BINDING_FORMAT, "phase": "infrastructure_premerge",
        "repository": REPOSITORY, "pr_number": 113,
        "branch": "research/final-mathematical-closure",
        "base_sha": context["original_base_sha"],
        "head_sha": context["head_sha"],
        "synthetic_sha": context["synthetic_sha"],
        "infrastructure_merge_sha": None,
    }
    candidate_bindings(record)
    need(record["base_sha"] == B113,
         "original immutable #113 base changed")
    return record


def deliver(context, run_id, reviewer_id, *, git,
            live=real_live, download=github_artifact_bytes):
    need(type(reviewer_id) is int and reviewer_id > 0,
         "real independent GitHub security review ID must be supplied")
    need(git("rev-parse", "HEAD") == context["synthetic_sha"] and
         git("cat-file", "-t", context["head_sha"]) == "commit" and
         git("show", "-s", "--format=%P", context["synthetic_sha"]).split() ==
             [context["original_base_sha"], context["head_sha"]],
         "GitHub synthetic merge does not use ordered exact B/H parents")
    # Use the true H Git blob; never the potentially modified local worktree.
    from infrastructure_acceptance_v2 import exact_committed_lake_blob
    manifest=exact_committed_lake_blob(context["head_sha"],git=git)
    raw, ids, verified = collect(
        context["head_sha"],run_id,live=live,download=download,
        committed_manifest=manifest)
    envelope = {
        "format": EVIDENCE_FORMAT,
        "target": detached_target(context),
        "source_bound_ci": [],  # Strict 12-context aggregate is a LATER gate.
        "historical_T": ids["T"], "historical_A2": ids["A2"],
        "security_review_id": reviewer_id,
    }
    # The noncircular v2 source-only envelope legitimately has zero CI
    # contexts. The later twelve-context aggregate uses the SAME schema.
    validate_envelope(envelope)
    return {
        "envelope": envelope,
        "zips": raw,
        "transport": {
            "format": FORMAT,
            "status": "REAL_ORIGINAL_ZIPS_AUTHENTICATED_REVIEW_PENDING",
            "head": context["head_sha"],
            "synthetic_sha": context["synthetic_sha"],
            "source_run_id": run_id,
            "originals": verified,
            "independent_security_review": False,
            "required_checks_successful": 0,
            "mathematical_acceptance": False,
            "owner_merge_authorized": False,
            "publication_authorized": False,
        },
    }


def deliver_merged(context, run_id, reviewer_id, *, git,
                   live=real_live, download=github_artifact_bytes):
    """Source-bound postmerge transportation; cannot infer merge authorization."""
    from pr113_historical_postmerge_v2 import FORMAT as MERGED_FORMAT, source_target
    need(type(reviewer_id) is int and reviewer_id > 0,
         "genuine historical independent review ID is mandatory")
    need(isinstance(context,dict) and
         context.get("original_base_sha") == B113 and
         context.get("merged_main_sha") == git("rev-parse","HEAD") and
         git("show","-s","--format=%P",
             context["merged_main_sha"]).split() ==
             [B113,context["reviewed_head_sha"]],
         "postmerge historical delivery requires authentic B/H/M")
    H=context["reviewed_head_sha"]
    from infrastructure_acceptance_v2 import exact_committed_lake_blob
    manifest=exact_committed_lake_blob(H,git=git)
    raw,ids,verified=collect(
        H,run_id,live=live,download=download,
        committed_manifest=manifest)
    envelope={
        "format":MERGED_FORMAT,
        "target":source_target(context),
        "source_bound_ci":[],
        "historical_T":ids["T"],"historical_A2":ids["A2"],
        "security_review_id":reviewer_id,
    }
    return {
        "envelope":envelope,
        "zips":raw,
        "transport":{
            "format":FORMAT,
            "status":"REAL_MERGED_SOURCE_ORIGINAL_ZIPS_RETRIEVED_REVIEW_PENDING",
            "head":H,
            "merged_main_sha":context["merged_main_sha"],
            "source_run_id":run_id,
            "originals":verified,
            "independent_security_review":False,
            "required_checks_successful":0,
            "mathematical_acceptance":False,
            "owner_merge_authorized":False,
            "publication_authorized":False,
        },
    }


def fresh_detached_path(path):
    from pr113_boundary_io import detached_destination
    return detached_destination(path, ROOT)


def source_git(*commands):
    """Return scalar Git identities as text and committed file bytes verbatim.

    Never pass bytes as a SHA comparison, and never use .strip() on a
    Git show REV:PATH payload. Both mistakes break authentic required checks.
    """
    import subprocess
    try:
        raw=subprocess.check_output(["git",*commands],cwd=ROOT,
              stderr=subprocess.DEVNULL,timeout=20)
    except (OSError,subprocess.CalledProcessError,
            subprocess.TimeoutExpired) as exc:
        raise DeliveryError("genuine Git object unavailable") from exc
    if (len(commands)>=2 and commands[0]=="show"
            and ":" in commands[1]):
        return raw
    return raw.decode("utf-8").strip()


def cli(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--producer-run-id", required=True, type=int)
    parser.add_argument("--security-review-id", required=True, type=int)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        if os.environ.get("GITHUB_EVENT_NAME") == "pull_request":
            context = actual_ci_event(git=source_git)
            result = deliver(context,args.producer_run_id,
                             args.security_review_id,git=source_git)
        elif os.environ.get("GITHUB_EVENT_NAME") == "push":
            from pr113_historical_postmerge_v2 import exact_main_event
            context = exact_main_event(git=source_git)
            result = deliver_merged(context,args.producer_run_id,
                                    args.security_review_id,git=source_git)
        else:
            raise DeliveryError("historical delivery requires a real main PR or push")
        out = fresh_detached_path(args.out)
        out.mkdir(parents=True,exist_ok=False)
        for k, name in (("T","historical_T.zip"),("A2","historical_A2.zip")):
            with (out/name).open("xb") as f:
                f.write(result["zips"][k])
        for key, name in (("envelope","historical_envelope.json"),
                          ("transport","historical_transport_unreviewed.json")):
            with (out/name).open("x",encoding="utf-8") as f:
                json.dump(result[key],f,sort_keys=True,indent=2)
                f.write("\n")
        print(json.dumps({
            "status":result["transport"]["status"],
            "head":result["transport"]["head"],
            "original_zip_count":2,
            "independent_review_authenticated":False,
        },sort_keys=True))
        return 0
    except (DeliveryError,ValueError,OSError,KeyError,TypeError) as exc:
        print("AUTHENTIC HISTORICAL DELIVERY BLOCKED:",exc,file=sys.stderr)
        return 2


if __name__=="__main__":
    raise SystemExit(cli())
