"""Detached V2 T/T2+A2 review packet, STRICTLY candidate evidence.

Requires actual active 30 reviewed Git blobs and the two genuine independent
historical execution reports. This cannot authenticate GitHub jobs or grant
reviewer/owner authority; those are separate external checks.
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
    inspect_zip, verify_A2_dependency_bridge, exact_committed_lake_blob,
)
from pr113_historical_intake_v2 import inspect_T_v2, inspect_A2_v2
from pr113_tooling_migration_v2 import audit as tooling_audit
from pr113_workflow_profile_v2 import audit as workflow_audit
from release_target import B113, T, REPOSITORY

ROOT = Path(__file__).resolve().parents[2]
FORMAT = "Permansson.PR113.DetachedHistoricalDualReviewPacket.v2"
SHA = re.compile(r"^[a-f0-9]{40}$")


class PacketError(ValueError):
    pass


def require(ok, reason):
    if not ok:
        raise PacketError(reason)


def digest(value):
    return hashlib.sha256(value).hexdigest()


def assemble(head, t_zip, a2_zip, *, git=real_git):
    require(isinstance(head, str) and SHA.fullmatch(head),
            "genuine versioned target head required")
    require(git("rev-parse", "HEAD") == head and
            git("cat-file", "-t", head) == "commit",
            "actual checkout did not match exact current head")
    require(type(t_zip) is bytes and type(a2_zip) is bytes
            and 0 < len(t_zip) <= 256 * 1024 * 1024
            and 0 < len(a2_zip) <= 256 * 1024 * 1024,
            "two independent bounded original artifact ZIPs required")
    workflows = workflow_audit(ROOT, head, phase="active")
    tooling = tooling_audit(ROOT, head, phase="active")
    require(tooling.get("workflow_profile_sha256") ==
                workflows["current_source_profile_sha256"] and
            tooling.get("current_reviewed_workflow_count") == 30,
            "versioned T2 review candidate not bound to same full profile")
    t_files = inspect_zip(t_zip)
    a_files = inspect_zip(a2_zip)
    t = inspect_T_v2(t_files, head,
                     profile_sha256=workflows["current_source_profile_sha256"])
    a = inspect_A2_v2(a_files, head)
    a["dependency_bridge_sha256"] = verify_A2_dependency_bridge(
        a_files, head, manifest_raw=exact_committed_lake_blob(head, git=git))
    return {
        "format": FORMAT,
        "status": "BOTH_HISTORICAL_25_AND_CURRENT_30_VERIFIED_FOR_REVIEW_ONLY",
        "repository": REPOSITORY,
        "source_head": head,
        "original_base": B113,
        "historical_archive_T": T,
        "historical_original_workflow_count": 25,
        "current_reviewed_workflow_count": 30,
        "full_workflow_profile_sha256": workflows["current_source_profile_sha256"],
        "T_zip_sha256": digest(t_zip),
        "A2_zip_sha256": digest(a2_zip),
        "T_execution": t,
        "A2_execution": a,
        "historical_T_unchanged": True,
        "historical_A2_unchanged": True,
        "source_bound_GitHub_job_authenticated": False,
        "independent_security_review": False,
        "owner_activation_authorized": False,
        "mathematical_acceptance": False,
        "merge_authorized": False,
        "publication_authorized": False,
    }


def cli(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head", required=True)
    p.add_argument("--T-artifact-zip", required=True, type=Path)
    p.add_argument("--A2-artifact-zip", required=True, type=Path)
    p.add_argument("--out", required=True, type=Path)
    args = p.parse_args(argv)
    try:
        output = args.out.absolute()
        require(not output.exists() and not output.is_symlink()
                and not output.is_relative_to(ROOT.resolve())
                and not any(x.is_symlink() for x in output.parents),
                "v2 review packet output must be detached, unsymlinked and new")
        t = args.T_artifact_zip.resolve(strict=True)
        a = args.A2_artifact_zip.resolve(strict=True)
        require(t != a and t.is_file() and a.is_file()
                and not args.T_artifact_zip.is_symlink()
                and not args.A2_artifact_zip.is_symlink(),
                "must provide two distinct original regular evidence ZIPs")
        report = assemble(args.head, t.read_bytes(), a.read_bytes())
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open("x", encoding="utf-8") as f:
            json.dump(report, f, sort_keys=True, indent=2)
            f.write("\n")
        print(json.dumps({"status": report["status"],
                          "source_head": report["source_head"]}, sort_keys=True))
        return 0
    except (OSError, ValueError, TypeError, KeyError) as exc:
        print("UNAPPROVED V2 HISTORICAL PACKET BLOCKED:", exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(cli())
