"""Deterministic ARC-01/04 exact Git-source review dossier, without authority.

Reads the real immutable historical T and current H Git objects plus the
source-staged 30-workflow contract; does NOT execute archive/Lean, download
producer artifacts, approve source or replace the required check.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

from pr113_boundary_io import detached_destination
from pr113_tooling_migration import (
    ROOT, T, B, SUPPLEMENT, TOOLING, EXPECTED_CHANGES,
    git, sha, exact_tree, ToolingMigrationError,
)
from pr113_tooling_migration_v2 import audit as boundary_audit
from pr113_workflow_profile_v2 import audit as workflow_audit, FORMAT as WF_FORMAT

FORMAT = "Permansson.PR113.ArchiveTCSourceReviewPacket.v1"
OID = re.compile(r"^[a-f0-9]{40}$")


class PacketError(ValueError):
    pass


def need(ok, why):
    if not ok:
        raise PacketError(why)


def produce(head, *, root=ROOT):
    root = Path(root).resolve(strict=True)
    boundary = boundary_audit(root, head, phase="staged")
    profile = workflow_audit(root, head, phase="staged")
    need(boundary.get("status") == "T2_EXACT_SOURCE_REVIEW_PENDING"
         and boundary.get("historical_archive_unchanged") is True
         and boundary.get("historical_packaged_tooling_files_verified") == 35
         and boundary.get("original_archive_T") == T
         and boundary.get("original_release_base_B") == B
         and boundary.get("reviewed_workflow_source_mode") == "staged",
         "full frozen T/H source audit absent")
    need(profile.get("format") == WF_FORMAT
         and profile.get("versioned_source_phase") == "staged"
         and profile.get("head_sha") == head
         and profile.get("historical_original_workflow_count") == 25
         and profile.get("current_reviewed_workflow_count") == 30
         and profile.get("retained_historical_count") == 23
         and profile.get("replacement_count") == 2
         and profile.get("addition_count") == 5
         and profile.get("independent_security_review") is False
         and profile.get("owner_activation_authorized") is False,
         "staged 25-to-30 Git-object contract absent")
    T_files, H_files = (
        exact_tree(root, rev, *TOOLING) for rev in (T, head))
    need(set(T_files) == set(H_files) and len(T_files) == 35,
         "complete 35-file canonical T/H membership not authenticated")
    records = []
    for path in sorted(T_files):
        old_mode, old_oid = T_files[path]
        cur_mode, cur_oid = H_files[path]
        need(old_mode == cur_mode
             and old_mode in ("100644", "100755")
             and OID.fullmatch(old_oid) and OID.fullmatch(cur_oid),
             "source path is not the immutable canonical regular Git file")
        old_bytes = git(root, "show", T + ":" + path)
        current_bytes = git(root, "show", head + ":" + path)
        records.append({
            "path": path, "mode": old_mode,
            "T_git_blob": old_oid, "H_git_blob": cur_oid,
            "T_sha256": sha(old_bytes), "H_sha256": sha(current_bytes),
            "changed": old_oid != cur_oid,
        })
    change_paths = {x["path"] for x in records if x["changed"]}
    need(change_paths == EXPECTED_CHANGES
         and len(boundary["changed_canonical_tooling"]) == 2
         and {row["path"] for row in boundary["changed_canonical_tooling"]}
             == change_paths,
         "T-to-H source contained an unreviewed change")
    virtual = profile.get("expected_source_blobs")
    need(type(virtual) is dict and len(virtual) == 30
         and all(type(k) is str and type(v) is str
                 and OID.fullmatch(v) for k,v in virtual.items()),
         "review-pending 30-source blob inventory is incomplete")
    raw_manifest = git(root, "show",
                       head + ":" + SUPPLEMENT + "/archive-manifest.json")
    need(sha(raw_manifest) == boundary["historical_manifest_sha256"],
         "original T archived manifest bytes changed since source audit")
    return {
        "format": FORMAT,
        "status": "REAL_GIT_SOURCE_ONLY_NO_HUMAN_AUTHORIZATION",
        "head_sha": head,
        "historical_T": T, "original_base_B": B,
        "historical_supplement_tree": boundary["historical_supplement_tree"],
        "historical_archive_manifest_sha256": sha(raw_manifest),
        "historical_tooling": records,
        "tooling_file_count": 35,
        "permitted_changed_paths": sorted(change_paths),
        "actual_active_workflows": 25,
        "proposed_active_workflows": 30,
        "retained_workflows": 23,
        "proposed_replacements": 2, "proposed_additions": 5,
        "virtual_workflow_git_blobs": dict(sorted(virtual.items())),
        "virtual_30_profile_sha256": profile["current_source_profile_sha256"],
        "mutable_action_refs_pending_independent_review":
            profile["inherited_mutable_action_refs"],
        "original_T_replay_runtime": "NOT_PRODUCED_BY_THIS_SOURCE_PACKET",
        "historical_A2_runtime": "NOT_PRODUCED_BY_THIS_SOURCE_PACKET",
        "original_GitHub_producer_zips":
            "NOT_AUTHENTICATED_BY_THIS_SOURCE_PACKET",
        "independent_security_review": False,
        "owner_activation_authorized": False,
        "current_required_archive_check_passed": False,
        "current_mathematical_acceptance": False,
        "PR113_merge_authorized": False,
        "publication_authorized": False,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head", required=True)
    parser.add_argument("--out", type=Path, required=True)
    options = parser.parse_args(argv)
    try:
        result = produce(options.head)
        out = detached_destination(options.out, ROOT)
        need(not out.exists() and not ROOT.resolve().is_relative_to(out),
             "review packet output must be new and detached from source")
        out.parent.mkdir(parents=True, exist_ok=True)
        with out.open("x", encoding="utf-8") as writer:
            json.dump(result, writer, sort_keys=True, indent=2)
            writer.write("\n")
        print(json.dumps({"status": result["status"], "H": options.head,
                          "canonical_files": result["tooling_file_count"],
                          "virtual_workflows": result["proposed_active_workflows"]},
                         sort_keys=True))
        return 0
    except (PacketError, ToolingMigrationError, OSError,
            ValueError, KeyError, TypeError) as exc:
        print("ARCHIVE_SOURCE_REVIEW_PACKET_BLOCKED:", exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
