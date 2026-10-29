"""Synthetic Git regression tests for immutable PR113 tooling migration.

Tests never authorize a historical rewrite, check-run acceptance or release.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import pr113_tooling_migration as migration


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=root, text=True).strip()


def commit(root: Path, title: str) -> str:
    subprocess.run(["git", "add", "-A"], cwd=root, check=True)
    subprocess.run(
        ["git", "-c", "user.name=SourceAudit",
         "-c", "user.email=audit@example.invalid",
         "commit", "-qm", title],
        cwd=root, check=True)
    return git(root, "rev-parse", "HEAD")


class SyntheticImmutableToolingTest(unittest.TestCase):
    def fixture(self, root: Path):
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        original = {
            "verification/integrity/workflow_contract.py": b"old reviewed workflows\n",
            "verification/integrity/tests/test_workflow.py": b"old reviewed tests\n",
            "verification/archive/verify_bundle.py": b"old offline replay\n",
            "archival/v0.2.0/README.md": b"frozen reproduction instructions\n",
        }
        for name, raw in original.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
        t = commit(root, "canonical historical tooling")
        frozen = root / migration.SUPPLEMENT
        frozen.mkdir(parents=True, exist_ok=True)
        rows = []
        for name, raw in sorted(original.items()):
            dest = frozen / "tooling" / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(raw)
            rows.append({
                "path": name,
                "blob": git(root, "rev-parse", t + ":" + name),
                "sha256": hashlib.sha256(raw).hexdigest(),
            })
        (frozen / "archive-manifest.json").write_text(json.dumps({
            "tooling": {"source_commit": t, "files": rows}
        }))
        for n in range(25):
            path = root / ".github/workflows" / ("reviewed-%02d.yml" % n)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("name: historical successor profile\n")
        b = commit(root, "sealed historical supplement and candidate workflows")
        for name in migration.EXPECTED_CHANGES:
            (root / name).write_text("new versioned candidate source\n")
        h = commit(root, "separate candidate tooling version")
        return t, b, h

    def test_exact_drift_produces_only_unapproved_proposal(self):
        with tempfile.TemporaryDirectory(prefix="pr113-synthetic-tooling-") as td:
            root = Path(td)
            t, b, h = self.fixture(root)
            report = migration.audit(root, h, historical_t=t, release_base=b)
            self.assertEqual(
                {x["path"] for x in report["changed_canonical_tooling"]},
                migration.EXPECTED_CHANGES)
            self.assertTrue(report["historical_archive_unchanged"])
            self.assertEqual(report["historical_packaged_tooling_files_verified"], 4)
            self.assertEqual(report["current_workflow_file_count"], 25)
            self.assertFalse(report["new_successor_T_approved"])
            self.assertFalse(report["independent_tooling_review"])
            self.assertFalse(report["mathematical_acceptance"])
            self.assertFalse(report["full_release_approved"])
            self.assertIn("DRAFT", report["status"])

    def test_extra_tooling_mutation_cannot_pass(self):
        with tempfile.TemporaryDirectory(prefix="pr113-extra-tool-") as td:
            root = Path(td)
            t, b, h = self.fixture(root)
            (root / "verification/archive/verify_bundle.py").write_text(
                "unapproved replay change\n")
            changed = commit(root, "new historical verifier mutation")
            with self.assertRaises(migration.ToolingMigrationError):
                migration.audit(root, changed, historical_t=t, release_base=b)

    def test_rewritten_historical_snapshot_cannot_pass(self):
        with tempfile.TemporaryDirectory(prefix="pr113-forged-archive-") as td:
            root = Path(td)
            t, b, h = self.fixture(root)
            path = (root / migration.SUPPLEMENT / "tooling" /
                    "verification/integrity/workflow_contract.py")
            path.write_bytes(b"rewritten archived proof tooling\n")
            changed = commit(root, "attempt to overwrite frozen T package")
            with self.assertRaises(migration.ToolingMigrationError):
                migration.audit(root, changed, historical_t=t, release_base=b)

    def test_pretend_checkout_and_missing_workflow_rejected(self):
        with tempfile.TemporaryDirectory(prefix="pr113-wrong-head-") as td:
            root = Path(td)
            t, b, h = self.fixture(root)
            with self.assertRaises(migration.ToolingMigrationError):
                migration.audit(root, b, historical_t=t, release_base=b)
            (root / ".github/workflows/reviewed-00.yml").unlink()
            changed = commit(root, "drop successor check")
            with self.assertRaises(migration.ToolingMigrationError):
                migration.audit(root, changed, historical_t=t, release_base=b)


if __name__ == "__main__":
    unittest.main()
