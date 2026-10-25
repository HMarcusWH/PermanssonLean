"""Fail-closed historical verification for a genuine ordered #113 main merge.

The original required checks run on both main PRs *and* main pushes. The PR
binding intentionally rejects merged PRs; using it on a main push would
permanently deadlock the release. This distinct v1 postmerge contract accepts
ONLY the genuine owner-authorized GitHub merge M with exact ordered B/H
parents, H's source tree, old real T/A2 producing ZIPs and authentic
independent approval of the actual H/artifact bytes.

This is code for a reviewed replacement gate, NOT current main authorization.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from final_closure_authenticate import (
    live as real_live, git as real_git, paginate as real_paginate,
)
from infrastructure_acceptance import (
    FORMAT as HISTORICAL_INPUT, ACTIVE_WORKFLOW, AUTHORITY_PATH,
    authenticate_original_zip, inspect_zip, inspect_T, inspect_A2,
    verify_A2_dependency_bridge, authority_policy, approved_security_review,
)
from release_target import B113, REPOSITORY

ROOT = Path(__file__).resolve().parents[2]
SHA = re.compile(r"^[0-9a-f]{40}$")
FORMAT = "Permansson.PR113.PostmergeHistoricalEvidence.v1"
TARGET = "Permansson.PR113.OrderedMainMergeTarget.v1"
RESULT = "Permansson.PR113.PostmergeRequiredHistoricalGate.v1"
JOBS = {
    "research": "Research Lean",
    "archive-reproducibility": "Research integrity",
}


class PostmergeError(ValueError):
    pass


def need(value, why):
    if not value:
        raise PostmergeError(why)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def exact_main_event(*, env=None, event_bytes=None, git=real_git, live=real_live):
    env = os.environ if env is None else env
    need(env.get("GITHUB_ACTIONS") == "true"
         and env.get("GITHUB_EVENT_NAME") == "push"
         and env.get("GITHUB_REF") == "refs/heads/main"
         and env.get("GITHUB_REPOSITORY") == REPOSITORY
         and env.get("GITHUB_JOB") in JOBS
         and env.get("GITHUB_WORKFLOW") == JOBS[env["GITHUB_JOB"]],
         "historical merged-source adapter must run in genuine required main job")
    M = env.get("GITHUB_SHA")
    need(isinstance(M, str) and SHA.fullmatch(M),
         "real main pushed merge commit missing")
    if event_bytes is None:
        filepath = Path(env.get("GITHUB_EVENT_PATH", ""))
        need(filepath.is_file() and not filepath.is_symlink()
             and 0 < filepath.stat().st_size <= 8*1024*1024,
             "main GitHub event file missing/unsafe")
        event_bytes = filepath.read_bytes()
    need(type(event_bytes) is bytes and
         0 < len(event_bytes) <= 8*1024*1024,
         "main event must be the original bounded GitHub JSON")
    try:
        event = json.loads(event_bytes)
    except (ValueError, TypeError) as exc:
        raise PostmergeError("main GitHub event JSON invalid") from exc
    need(isinstance(event,dict) and
         event.get("ref") == "refs/heads/main" and
         event.get("after") == M and
         (event.get("repository") or {}).get("full_name") == REPOSITORY,
         "main push event does not bind original source")
    try:
        run_id = int(env.get("GITHUB_RUN_ID", ""))
        attempt = int(env.get("GITHUB_RUN_ATTEMPT", ""))
    except (ValueError, TypeError) as exc:
        raise PostmergeError("main source run identity missing") from exc
    need(run_id > 0 and attempt > 0,
         "main source run IDs invalid")
    need(git("rev-parse","HEAD") == M and
         git("cat-file","-t",M) == "commit",
         "source checkout is not exact genuine pushed main")
    parents = git("show","-s","--format=%P",M).split()
    need(len(parents) == 2 and parents[0] == B113 and
         SHA.fullmatch(parents[1]) is not None and
         git("cat-file","-t",parents[1]) == "commit" and
         git("rev-parse",M+"^{tree}") ==
             git("rev-parse",parents[1]+"^{tree}"),
         "merged main must be real ordered original B/H with reviewed H tree")
    H = parents[1]
    pr = live("/pulls/113")
    main = live("/branches/main")
    need(isinstance(pr,dict) and pr.get("number") == 113
         and pr.get("state") == "closed" and pr.get("merged") is True
         and pr.get("merge_commit_sha") == M
         and (pr.get("head") or {}).get("sha") == H
         and isinstance(main,dict)
         and (main.get("commit") or {}).get("sha") == M,
         "merged infrastructure PR and actual remote main disagree")
    return {
        "original_base_sha": B113, "reviewed_head_sha": H,
        "merged_main_sha": M, "github_run_id": run_id,
        "github_run_attempt": attempt, "github_job": env["GITHUB_JOB"],
        "github_event_sha256": sha(event_bytes),
    }


def source_target(context):
    return {
        "format": TARGET, "repository": REPOSITORY,
        "pr_number": 113,
        "original_base_sha": context["original_base_sha"],
        "reviewed_head_sha": context["reviewed_head_sha"],
        "merged_main_sha": context["merged_main_sha"],
    }


def check_historical_merged(envelope, t_zip, a2_zip, *,
                            event_context, git=real_git, live=real_live,
                            paginate=real_paginate):
    need(isinstance(envelope,dict) and
         set(envelope) == {
             "format","target","historical_T","historical_A2",
             "security_review_id","source_bound_ci"
         } and envelope.get("format") == FORMAT
         and envelope.get("target") == source_target(event_context)
         and envelope.get("source_bound_ci") == [],
         "historical postmerge target not bound to real M/B/H")
    H = event_context["reviewed_head_sha"]
    M = event_context["merged_main_sha"]
    workflow = git("show", H+":"+ACTIVE_WORKFLOW)
    need(isinstance(workflow,str) and
         workflow.startswith("# Review-pending source-controlled") and
         "historical-T-and-H-unreviewed" in workflow and
         "historical-A2-and-H-unreviewed" in workflow and
         git("show",M+":"+ACTIVE_WORKFLOW) == workflow,
         "reviewed historical T/A2 source not identical in real M")
    t = authenticate_original_zip(
        "T",envelope["historical_T"],t_zip,H,live=live)
    a = authenticate_original_zip(
        "A2",envelope["historical_A2"],a2_zip,H,live=live)
    archived=inspect_T(inspect_zip(t_zip),H)
    current=inspect_A2(inspect_zip(a2_zip),H)
    current["dependency_bridge_sha256"] = verify_A2_dependency_bridge(
        inspect_zip(a2_zip),H,
        manifest_raw=git("show",H+":lake-manifest.json"))
    policy=authority_policy(H,git=git)
    reviewer_attestation={
        "head_sha":H,
        "workflow_sha256":sha(workflow.encode("utf-8")),
        "T_artifact_sha256":sha(t_zip),
        "A2_artifact_sha256":sha(a2_zip),
        "original_base_sha":B113,
    }
    pr=live("/pulls/113")
    approved_security_review(
        envelope["security_review_id"],(pr.get("user") or {}).get("login"),
        H,reviewer_attestation,policy,paginate=paginate)
    return {
        "format":RESULT,
        "status":"MERGED_HISTORICAL_T_AND_A2_REVERIFIED_UNDER_REVIEWED_SOURCE",
        "original_base_sha":B113,
        "head_sha":H,
        "merged_main_sha":M,
        "original_T":t,"original_A2":a,
        "original_T_checks":archived,"original_A2_checks":current,
        "security_review_id":envelope["security_review_id"],
        "independent_security_review_authenticated":True,
        "required_ci_successful":0,
        "independent_mathematical_review":False,
        "accepted_original_cases":0,"accepted_new_claims":0,
        "owner_merge_authorized":False,
        "publication_authorized":False,
        "full_release_approved":False,
    }


def verify(envelope,t_zip,a2_zip,*,env=None,event_bytes=None,git=real_git,
           live=real_live,paginate=real_paginate):
    context=exact_main_event(env=env,event_bytes=event_bytes,git=git,live=live)
    return check_historical_merged(
        envelope,t_zip,a2_zip,event_context=context,
        git=git,live=live,paginate=paginate)
