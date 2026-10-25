"""Produce an unapproved, detached historical T/T2 + A2 review packet.

Both historical original legs must really execute before this packet can be
generated. The packet checks exact-source bytes, original/new historical
report content and staged workflow closure. It does NOT authenticate a live
GitHub producing job; that is deliberately reserved for the separate
infrastructure_acceptance gate after independent security review.

Neither input JSON nor a candidate status can authorize workflow activation,
a mathematical result, a merge or publication.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

from final_closure_authenticate import git as real_git
from infrastructure_acceptance import (
    InfrastructureError, inspect_zip, inspect_T, inspect_A2,
    verify_A2_dependency_bridge,
)
from pr113_tooling_migration import audit as tooling_audit
from pr113_successor_workflow_profile import audit as workflow_profile_audit
from release_target import B113, T, REPOSITORY

ROOT = Path(__file__).resolve().parents[2]
FORMAT = "Permansson.PR113.DetachedHistoricalDualReviewPacket.v1"
HEAD_SHA = re.compile(r"^[a-f0-9]{40}$")


class ReviewPacketError(ValueError):
    pass


def need(condition, message):
    if not condition:
        raise ReviewPacketError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def assemble(head, original_t_zip, original_a2_zip, *,
             git=real_git, audit_tooling=None, audit_workflows=None):
    need(isinstance(head, str) and HEAD_SHA.fullmatch(head),
         "historical review requires exact real Git head SHA")
    need(git("rev-parse", "HEAD") == head and
         git("cat-file", "-t", head) == "commit",
         "candidate checkout not the actual exact-H Git commit")
    need(type(original_t_zip) is bytes and
         type(original_a2_zip) is bytes,
         "actual original historical ZIP bytes required")
    t_files = inspect_zip(original_t_zip)
    a2_files = inspect_zip(original_a2_zip)
    t = inspect_T(t_files, head)
    a2 = inspect_A2(a2_files, head)
    a2["dependency_bridge_sha256"] = verify_A2_dependency_bridge(
        a2_files, head, manifest_raw=git("show", head+":lake-manifest.json"))
    if audit_tooling is None:
        audit_tooling = lambda h: tooling_audit(ROOT, h)
    if audit_workflows is None:
        audit_workflows = workflow_profile_audit
    tooling = audit_tooling(head)
    profile = audit_workflows(head)
    need(isinstance(tooling, dict) and
         tooling.get("source_commit_sha") == head and
         tooling.get("original_archive_T") == T and
         tooling.get("original_release_base_B") == B113 and
         tooling.get("status") ==
             "DRAFT_NEEDS_OWNER_AND_INDEPENDENT_SECURITY_REVIEW" and
         tooling.get("historical_archive_unchanged") is True and
         tooling.get("current_workflow_file_count") == 25 and
         len(tooling.get("changed_canonical_tooling", [])) == 2 and
         tooling.get("new_successor_T_approved") is False and
         tooling.get("independent_tooling_review") is False,
         "original T/H unchanged-history tooling audit not complete")
    need(isinstance(profile, dict) and
         profile.get("head_sha") == head and
         profile.get("historical_T") == T and
         profile.get("original_base") == B113 and
         profile.get("status") ==
             "EXACT_25_PLUS_5_SOURCE_PROFILE_CANDIDATE_NOT_ACTIVATED" and
         profile.get("original_workflow_count") == 25 and
         profile.get("successor_proposal_count") == 5 and
         profile.get("active_profile_changed") is False and
         profile.get("independent_security_review") is False and
         profile.get("owner_activation_authorized") is False,
         "unapproved 25+5 workflow review profile is incomplete or activated")
    return {
        "format": FORMAT,
        "status": "BOTH_HISTORICAL_SOURCE_LEGS_VERIFIED_FOR_REVIEW_ONLY",
        "repository": REPOSITORY,
        "current_head": head,
        "original_base": B113,
        "historical_archive_T": T,
        "original_T_H_zip_sha256": sha(original_t_zip),
        "original_A2_H_zip_sha256": sha(original_a2_zip),
        "T_execution": t,
        "A2_execution": a2,
        "canonical_tooling_changes": tooling["changed_canonical_tooling"],
        "workflow_profile_sha256": profile["profile_sha256"],
        "historical_T_unchanged": True,
        "historical_A2_unchanged": True,
        "source_bound_GitHub_job_authenticated": False,
        "independent_security_review": False,
        "owner_activation_authorized": False,
        "mathematical_acceptance": False,
        "merge_authorized": False,
        "publication_authorized": False,
        "next_action": "Authenticate real current-H GitHub producing jobs and obtain independent security review of exact T/T2+A2+25+5 source before separate owner activation.",
    }


def detached_regular_file(path):
    requested = Path(path).absolute()
    need(".." not in requested.parts and
         not any(x.is_symlink() for x in (requested,*requested.parents)),
         "symlinked historical artifact or destination not permitted")
    result = requested.resolve(strict=True)
    need(result.is_file() and not result.is_symlink(),
         "original artifact must be a real regular file")
    return result


def cli(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head", required=True)
    p.add_argument("--T-artifact-zip", type=Path, required=True)
    p.add_argument("--A2-artifact-zip", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    args = p.parse_args(argv)
    try:
        dest = args.out.absolute()
        need(not dest.exists() and not dest.is_symlink() and
             not dest.is_relative_to(ROOT.resolve()) and
             not any(x.is_symlink() for x in dest.parents),
             "review packet must be a fresh detached output")
        t = detached_regular_file(args.T_artifact_zip)
        a2 = detached_regular_file(args.A2_artifact_zip)
        need(t != a2 and t != dest and a2 != dest,
             "independent historical artifacts and output must be disjoint")
        need(0 < t.stat().st_size <= 256*1024*1024 and
             0 < a2.stat().st_size <= 256*1024*1024,
             "historical source artifact exceeds bounded ZIP size")
        report = assemble(args.head, t.read_bytes(), a2.read_bytes())
        dest.parent.mkdir(parents=True, exist_ok=True)
        with dest.open("x", encoding="utf-8") as f:
            json.dump(report, f, indent=2, sort_keys=True)
            f.write("\n")
        print(json.dumps({"status": report["status"],
                          "current_head": report["current_head"]},
                         sort_keys=True))
        return 0
    except (ReviewPacketError, InfrastructureError, OSError, ValueError,
            KeyError, TypeError) as exc:
        print("DUAL HISTORICAL REVIEW PACKET NOT ACCEPTED:", exc,
              file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(cli())
