"""T2 30-workflow review candidate. The v1 25-file audit remains unchanged.

The historical accepted T archive is read at its actual Git revision and
compared byte-for-byte with the fixed supplemental bundle. Both known tooling
edits are enumerated, never turned into a global wildcard exception.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import sys

from pr113_tooling_migration import (
    ROOT, T, B, SUPPLEMENT, TOOLING, EXPECTED_CHANGES,
    ToolingMigrationError, exact_tree, git, sha, require, SHA40,
)
from pr113_workflow_profile_v2 import audit as audit_workflows
from pr113_boundary_io import strict_json_object

FORMAT = "Permansson.PR113.ToolingMigrationCandidate.v2"


def audit(root, head, *, phase="staged"):
    root = Path(root).resolve(strict=True)
    require(isinstance(head, str) and SHA40.fullmatch(head),
            "invalid versioned current head identity")
    require(git(root, "rev-parse", "HEAD").decode().strip() == head,
            "candidate checkout no longer matches its actual commit")
    for ancestor in (T, B):
        git(root, "merge-base", "--is-ancestor", ancestor, head)
    original_tree = git(root, "rev-parse", B + ":" + SUPPLEMENT).strip()
    actual_tree = git(root, "rev-parse", head + ":" + SUPPLEMENT).strip()
    require(original_tree == actual_tree,
            "historical accepted supplement changed from original base")
    manifest_raw = git(root, "show", head + ":" + SUPPLEMENT +
                       "/archive-manifest.json")
    try:
        manifest = strict_json_object(manifest_raw)
    except (ValueError, UnicodeError) as exc:
        raise ToolingMigrationError("original T archive manifest malformed") from exc
    tooling = manifest.get("tooling") if isinstance(manifest, dict) else None
    require(isinstance(tooling, dict) and tooling.get("source_commit") == T,
            "original historical T source not pinned by archived manifest")
    # The original manifest is a COMPLETE 35-file historical source closure.
    # A self-consistent partial repackage is NOT the approved T artifact.
    old = exact_tree(root, T, *TOOLING)
    current = exact_tree(root, head, *TOOLING)
    files = tooling.get("files")
    require(isinstance(files, list) and len(files) == len(old) == 35,
            "historical packaged T closure is not the complete 35-file set")
    declared = set()
    for row in files:
        require(isinstance(row, dict)
                and set(row) == {"path", "blob", "sha256"},
                "historical T manifest row invalid or has unknown keys")
        path, oid, digest = row["path"], row["blob"], row["sha256"]
        require(isinstance(path, str) and path in old
                and path not in declared and
                isinstance(oid, str) and SHA40.fullmatch(oid)
                and isinstance(digest, str) and
                re.fullmatch(r"[0-9a-f]{64}", digest),
                "historical T manifest has missing, foreign or duplicate source")
        declared.add(path)
        at_t = git(root, "show", T + ":" + path)
        packaged = git(root, "show", head + ":" + SUPPLEMENT +
                       "/tooling/" + path)
        original_oid = git(root, "rev-parse", T + ":" + path).decode().strip()
        require(at_t == packaged and sha(at_t) == digest and
                oid == original_oid == old[path][1],
                "historical T file is not the byte-exact frozen member: " + path)
    require(declared == set(old), "historical packaged T omits an original file")
    require(set(old) == set(current), "T2 changed historical tooling membership")
    require(all(old[path][0] == current[path][0] for path in old),
            "historical tooling file mode changed (not an approved migration)")
    changed = sorted(path for path in old if old[path][1] != current[path][1])
    require(set(changed) == EXPECTED_CHANGES,
            "changed integrity verifier surface not limited to named two files")
    profile = audit_workflows(root, head, phase=phase)
    require(profile.get("current_reviewed_workflow_count") == 30
            and profile.get("historical_original_workflow_count") == 25
            and profile.get("independent_security_review") is False,
            "current 30-workflow source profile not authenticated")
    return {
        "format": FORMAT,
        "status": "T2_EXACT_SOURCE_REVIEW_PENDING",
        "source_commit_sha": head,
        "original_archive_T": T,
        "original_release_base_B": B,
        "historical_supplement_tree": actual_tree.decode(),
        "historical_manifest_sha256": sha(manifest_raw),
        "historical_packaged_tooling_files_verified": len(files),
        "changed_canonical_tooling": [
            {"path": path, "T_blob": old[path][1],
             "H_blob": current[path][1]} for path in changed],
        "historical_original_workflow_count": 25,
        "current_reviewed_workflow_count": 30,
        "reviewed_workflow_source_mode": phase,
        "workflow_profile_sha256": profile["current_source_profile_sha256"],
        "inherited_mutable_action_refs": profile["inherited_mutable_action_refs"],
        "historical_archive_unchanged": True,
        "new_successor_T_approved": False,
        "independent_security_review": False,
        "owner_activation_authorized": False,
        "mathematical_acceptance": False,
        "full_release_approved": False,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head", required=True)
    parser.add_argument("--phase", choices=("staged", "active"), default="staged")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        result = audit(ROOT, args.head, phase=args.phase)
        dest = args.out.absolute()
        require(not dest.exists() and not dest.is_symlink()
                and not dest.is_relative_to(ROOT.resolve())
                and not any(p.is_symlink() for p in dest.parents),
                "v2 candidate report output must be fresh, detached, unsymlinked")
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                        encoding="utf-8")
        print(json.dumps({"status": result["status"],
                          "head_sha": result["source_commit_sha"],
                          "current_workflows": result["current_reviewed_workflow_count"]},
                         sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError) as exc:
        print("T2 UNAPPROVED SOURCE PROFILE REJECTED:", exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
