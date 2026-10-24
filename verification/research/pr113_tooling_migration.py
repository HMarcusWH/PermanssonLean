"""Read-only PR113 successor-tooling preflight; NEVER historical release approval.

Compare the immutable v0.2.0 packaged T snapshot with the genuine Git T/B/H
objects. Report only the two separately reviewable integrity-tooling edits.
Do not change the original v0.2.0 verifier, archive manifest, workflow gates,
review receipts or historical artifact. The report deliberately cannot
declare mathematical or scholarly acceptance.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
T = "71cc34fa0bc4b639c05d2ec5f39f0b88afd56388"
B = "17c315f7df7abf457eb94d393bd526d46da6f6f4"
SUPPLEMENT = "archival/v0.2.0/supplement-1"
TOOLING = ("verification/integrity", "verification/archive",
           "archival/v0.2.0/README.md")
EXPECTED_CHANGES = frozenset((
    "verification/integrity/workflow_contract.py",
    "verification/integrity/tests/test_workflow.py",
))
SHA40 = re.compile(r"^[0-9a-f]{40}$")
MAX_OBJECT = 5 * 1024 * 1024


class ToolingMigrationError(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ToolingMigrationError(message)


def git(root: Path, *args: str) -> bytes:
    try:
        result = subprocess.run(
            ["git", *args], cwd=root, capture_output=True, timeout=45)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ToolingMigrationError("Git source object unavailable") from exc
    if result.returncode != 0 or len(result.stdout) > MAX_OBJECT:
        raise ToolingMigrationError("Git rejected or oversized source object: "
                                    + " ".join(args[:3]))
    return result.stdout


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def exact_tree(root: Path, rev: str, *prefixes: str) -> dict[str, tuple[str, str]]:
    raw = git(root, "ls-tree", "-r", "-z", "--full-tree", rev, "--", *prefixes)
    result = {}
    for item in raw.split(b"\0"):
        if not item:
            continue
        try:
            header, name = item.split(b"\t", 1)
            mode, kind, oid = header.decode("ascii").split()
            path = name.decode("utf-8")
        except (ValueError, UnicodeError) as exc:
            raise ToolingMigrationError("Malformed Git tree entry") from exc
        require(kind == "blob" and mode in ("100644", "100755")
                and path not in result, "Unsafe duplicate/nonfile Git tooling")
        result[path] = (mode, oid)
    return result


def audit(root: Path, head: str, *,
          historical_t: str = T, release_base: str = B) -> dict:
    root = Path(root).resolve()
    require(all(isinstance(k, str) and SHA40.fullmatch(k)
                for k in (head, historical_t, release_base)),
            "Invalid immutable Git object ID")
    require(git(root, "rev-parse", "HEAD").decode().strip() == head,
            "Checkout does not match requested source head")
    for old in (historical_t, release_base):
        try:
            git(root, "merge-base", "--is-ancestor", old, head)
        except ToolingMigrationError as exc:
            raise ToolingMigrationError(
                "Historical source/base is not an ancestor of candidate") from exc
    old_snapshot = git(root, "rev-parse", f"{release_base}:{SUPPLEMENT}").strip()
    new_snapshot = git(root, "rev-parse", f"{head}:{SUPPLEMENT}").strip()
    require(old_snapshot == new_snapshot,
            "Historical supplement bytes changed since accepted base B")
    manifest_raw = git(root, "show", f"{head}:{SUPPLEMENT}/archive-manifest.json")
    manifest = json.loads(manifest_raw)
    data = manifest.get("tooling")
    require(isinstance(data, dict) and
            data.get("source_commit") == historical_t,
            "Historical archive no longer binds the genuine T commit")
    rows = data.get("files")
    require(isinstance(rows, list) and len(rows) >= 3,
            "Historical packaged tooling closure is incomplete")
    for row in rows:
        require(isinstance(row, dict), "Malformed frozen tooling declaration")
        path, blob, expected = row.get("path"), row.get("blob"), row.get("sha256")
        require(isinstance(path, str) and
                (path.startswith("verification/integrity/") or
                 path.startswith("verification/archive/") or
                 path == "archival/v0.2.0/README.md") and
                isinstance(blob, str) and SHA40.fullmatch(blob) and
                isinstance(expected, str) and re.fullmatch("[0-9a-f]{64}", expected),
                "Untrusted tooling closure member")
        original = git(root, "show", f"{historical_t}:{path}")
        packaged = git(root, "show", f"{head}:{SUPPLEMENT}/tooling/{path}")
        actual_oid = git(root, "rev-parse", f"{historical_t}:{path}").decode().strip()
        require(original == packaged and sha(original) == expected
                and actual_oid == blob,
                "Historical packaged T object failed independent byte comparison: "
                + path)

    original = exact_tree(root, historical_t, *TOOLING)
    current = exact_tree(root, head, *TOOLING)
    require(set(original) == set(current),
            "Canonical T-to-H tooling file membership was changed")
    changed = sorted(path for path in original
                     if current[path] != original[path])
    require(set(changed) == EXPECTED_CHANGES,
            "Unexpected canonical T-to-H tooling divergence: " + repr(changed))
    workflows = exact_tree(root, head, ".github/workflows")
    require(len(workflows) == 25 and
            all(path.endswith((".yml", ".yaml"))
                and path.startswith(".github/workflows/")
                for path in workflows),
            "Successor candidate no longer has the exact 25-workflow inventory")
    return {
        "format": "Permansson.PR113.ToolingMigrationProposal.v1",
        "status": "DRAFT_NEEDS_OWNER_AND_INDEPENDENT_SECURITY_REVIEW",
        "source_commit_sha": head,
        "original_archive_T": historical_t,
        "original_release_base_B": release_base,
        "historical_supplement_tree": new_snapshot.decode(),
        "historical_manifest_sha256": sha(manifest_raw),
        "historical_packaged_tooling_files_verified": len(rows),
        "current_workflow_file_count": len(workflows),
        "changed_canonical_tooling": [
            {"path": path,
             "T_blob": original[path][1], "H_blob": current[path][1]}
            for path in changed
        ],
        "historical_archive_unchanged": True,
        "new_successor_T_approved": False,
        "independent_tooling_review": False,
        "mathematical_acceptance": False,
        "full_release_approved": False,
        "request": "Authorize a new versioned T/R release closure without "
                   "rewriting the immutable v0.2.0 archive.",
    }


def main(argv=None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--head", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        target = args.output.resolve()
        require(not target.exists() and
                not target.is_relative_to(ROOT.resolve()) and
                not ROOT.resolve().is_relative_to(target),
                "Tooling proposal must be detached from the Git checkout")
        result = audit(ROOT, args.head)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n",
                          encoding="utf-8")
        print(json.dumps({"status": result["status"],
                          "changed_paths": [r["path"] for r in
                                            result["changed_canonical_tooling"]]}))
        return 0
    except (ToolingMigrationError, OSError, ValueError, KeyError) as exc:
        print("PR113 TOOLING MIGRATION BLOCKED:", exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
