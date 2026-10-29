"""Independently reverify the immutable approved PR113 historical gate on descendants.

Run original historical T/T2/A2 *consumer source* from the authentic M113
worktree, never by replaying a forged PR113 event in a successor required job.
This does not certify any new source, mathematics, merge or publication.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from pr113_boundary_io import detached_destination, strict_json_object
from pr113_lifecycle_source_v3 import actual_source

ROOT = Path(__file__).resolve().parents[2]
FORMAT = "Permansson.PR113.InheritedHistoricalInfrastructure.v3"

# This child is executed inside the independently authenticated immutable M113
# tree. Its imports resolve to M113 source, not to the successor PR source.
# No GITHUB_EVENT_NAME, GITHUB_SHA or event JSON is forged or rewritten.
CHILD = r"""
import json,sys
from pr113_historical_artifact_delivery_v2 import collect
from pr113_historical_postmerge_v2 import (
    check_historical_merged, source_target, FORMAT as MERGED_FORMAT,
)
from infrastructure_acceptance_v2 import exact_committed_lake_blob
from release_target import B113
from final_closure_authenticate import REQUIRED, authenticated_checks
H,M,run_id,reviewer_id=sys.argv[1:]
run_id=int(run_id)
reviewer_id=int(reviewer_id)
if run_id <= 0 or reviewer_id <= 0:
    raise ValueError("historical source run/review IDs must be positive")
context={"original_base_sha":B113,"reviewed_head_sha":H,
         "merged_main_sha":M}
bytes_by_kind,ids,verified=collect(
    H,run_id,committed_manifest=exact_committed_lake_blob(H))
envelope={
    "format":MERGED_FORMAT,"target":source_target(context),
    "source_bound_ci":[],"historical_T":ids["T"],
    "historical_A2":ids["A2"],"security_review_id":reviewer_id,
}
receipt=check_historical_merged(
    envelope,bytes_by_kind["T"],bytes_by_kind["A2"],
    event_context=context)
required=authenticated_checks(H)
# Assertions can disappear with python -O or PYTHONOPTIMIZE. Use explicit
# checks in every inherited historical source/review authentication path.
if (len(REQUIRED) != 12 or not isinstance(required,dict)
        or not set(REQUIRED) <= set(required)):
    raise ValueError("historical source lacks all twelve live required checks")
for name in REQUIRED:
    check=required[name]
    if (not isinstance(check,dict)
            or check.get("head_sha") != H
            or check.get("status") != "completed"
            or check.get("conclusion") != "success"
            or type(check.get("id")) is not int
            or check["id"] <= 0):
        raise ValueError("unbound or unsuccessful historical check: " + name)
if receipt.get("status") != (
        "MERGED_HISTORICAL_T_AND_A2_REVERIFIED_UNDER_REVIEWED_SOURCE"):
    raise ValueError("original M113 historical replay has not succeeded")
if receipt.get("independent_security_review_authenticated") is not True:
    raise ValueError("original M113 security review is not authenticated")
if type(receipt.get("required_ci_successful")) is not int or (
        receipt["required_ci_successful"] != 0):
    raise ValueError("historical-only result cannot assert current CI approval")
print(json.dumps({
    "source_head_sha":H,"merged_main_sha":M,
    "historical_original_producer_run_id":run_id,
    "security_review_id":reviewer_id,
    "historical_status":receipt["status"],
    "historical_original_workflow_count":25,
    "current_reviewed_workflow_count":30,
    "original_required_context_count":len(REQUIRED),
    "historical_security_review_authenticated":True,
    "historical_T_and_A2_genuine":True,
    "new_mathematical_acceptance":False,
    "publication_authorized":False,
},sort_keys=True))
"""


class InheritanceError(ValueError):
    pass


def demand(ok, why):
    if not ok:
        raise InheritanceError(why)


def verify_child_report(result, lifecycle, *, run_id, reviewer_id):
    demand(isinstance(result, dict)
           and result.get("source_head_sha") == lifecycle["infrastructure_head_sha"]
           and result.get("merged_main_sha") == lifecycle["infrastructure_merge_sha"]
           and type(result.get("historical_original_producer_run_id")) is int
           and result["historical_original_producer_run_id"] == run_id
           and type(result.get("security_review_id")) is int
           and result["security_review_id"] == reviewer_id
           and result.get("historical_status") ==
                "MERGED_HISTORICAL_T_AND_A2_REVERIFIED_UNDER_REVIEWED_SOURCE"
           and result.get("original_required_context_count") == 12
           and result.get("historical_original_workflow_count") == 25
           and result.get("current_reviewed_workflow_count") == 30
           and result.get("historical_security_review_authenticated") is True
           and result.get("historical_T_and_A2_genuine") is True
           and result.get("new_mathematical_acceptance") is False
           and result.get("publication_authorized") is False,
           "inherited historical source validation is incomplete")
    return {
        "format": FORMAT,
        "status": "PR113_HISTORICAL_SOURCE_REVERIFIED_FOR_AUTHENTIC_DESCENDANT",
        "current_source_sha": lifecycle["source_commit_sha"],
        "current_phase": lifecycle["phase"],
        "current_github_run_id": lifecycle["github_run_id"],
        "current_github_run_attempt": lifecycle["github_run_attempt"],
        "historical_source_head_sha": result["source_head_sha"],
        "historical_merged_main_sha": result["merged_main_sha"],
        "historical_original_producer_run_id": run_id,
        "historical_security_review_id": reviewer_id,
        "original_required_context_count": 12,
        "current_required_ci_accepted": False,
        "new_mathematical_acceptance": False,
        "owner_merge_authorized": False,
        "publication_authorized": False,
    }


def verify(producer_run_id, security_review_id, *, lifecycle=None):
    demand(type(producer_run_id) is int and producer_run_id > 0
           and type(security_review_id) is int and security_review_id > 0,
           "genuine original run/review IDs required")
    lifecycle = actual_source() if lifecycle is None else lifecycle
    demand(isinstance(lifecycle, dict) and
           lifecycle.get("phase") in ("main_descendant_pr",
                                      "main_descendant_push")
           and lifecycle.get("infrastructure_merge_sha")
           and lifecycle.get("infrastructure_head_sha"),
           "historical inheritance cannot replace original PR113 T/A2 required gate")
    token = os.environ.get("GITHUB_TOKEN")
    demand(isinstance(token, str) and bool(token),
           "GitHub token required for actual historical evidence revalidation")
    M = lifecycle["infrastructure_merge_sha"]
    H = lifecycle["infrastructure_head_sha"]
    with tempfile.TemporaryDirectory(prefix="pr113-historical-inheritance-") as temp:
        old = Path(temp) / "reviewed-M113"
        try:
            subprocess.run(["git", "-C", str(ROOT), "worktree", "add", "--detach",
                            str(old), M], stdout=subprocess.DEVNULL,
                           stderr=subprocess.PIPE, check=True, timeout=60)
            found = subprocess.check_output(
                ["git", "-C", str(old), "rev-parse", "HEAD"],
                timeout=20).decode().strip()
            demand(found == M, "historical executor checkout not exact M113")
            executed = subprocess.run(
                [sys.executable, "-B", "-c",
                 "import sys;sys.path.insert(0, 'verification/research');" + CHILD,
                 H, M, str(producer_run_id), str(security_review_id)],
                cwd=old, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                check=False, timeout=900)
            demand(executed.returncode == 0
                   and len(executed.stdout) <= 32768
                   and len(executed.stdout) > 0,
                   "actual M113 historical source/review verification failed")
            report = strict_json_object(executed.stdout, max_bytes=32768)
            return verify_child_report(report, lifecycle,
                                       run_id=producer_run_id,
                                       reviewer_id=security_review_id)
        except (OSError, subprocess.SubprocessError) as exc:
            raise InheritanceError("authentic original M113 execution unavailable") from exc
        finally:
            if old.exists():
                subprocess.run(["git", "-C", str(ROOT), "worktree", "remove",
                                "--force", str(old)],
                               stdout=subprocess.DEVNULL,
                               stderr=subprocess.DEVNULL, timeout=60,
                               check=False)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--producer-run-id", type=int, required=True)
    ap.add_argument("--security-review-id", type=int, required=True)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args(argv)
    try:
        output = detached_destination(args.out, ROOT)
        receipt = verify(args.producer_run_id, args.security_review_id)
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open("x", encoding="utf-8") as file:
            json.dump(receipt, file, sort_keys=True, indent=2)
            file.write("\n")
        print(json.dumps({"status": receipt["status"],
                          "current_source_sha": receipt["current_source_sha"]}))
        return 0
    except (InheritanceError, OSError, KeyError, ValueError) as exc:
        print("INHERITED_PR113_SOURCE_REVALIDATION_BLOCKED", exc,
              file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
