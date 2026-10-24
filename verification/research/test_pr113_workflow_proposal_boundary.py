"""Fail closed on unreviewed workflow proposals becoming silently executable.

This test protects the original 25-workflow boundary. It checks exact Git
blobs, so text, file modes, or path substitutions cannot masquerade as review.
It never authorizes a new workflow or trust migration.
"""
from __future__ import annotations
import json
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[2]
PROPOSALS = ROOT / "docs/operations/pr113_unapproved_workflows"
ACTIVE = ".github/workflows/"


def git(*args):
    return subprocess.check_output(
        ["git", *args], cwd=ROOT, stderr=subprocess.DEVNULL, timeout=20
    ).decode("utf-8").strip()


def source_manifest():
    manifest = json.loads((PROPOSALS / "manifest.json").read_bytes())
    if (manifest.get("format") !=
            "Permansson.PR113.UnreviewedWorkflowProposals.v1"):
        raise ValueError("wrong workflow proposal manifest")
    return manifest


class WorkflowProposalBoundary(unittest.TestCase):
    def test_original_workflow_set_retained_without_silent_new_workflows(self):
        from verification.integrity.workflow_contract import APPROVED_WORKFLOWS
        active = [x for x in git("ls-tree", "-r", "--name-only", "HEAD",
                                  "--", ".github/workflows").splitlines()
                  if x.startswith(ACTIVE)]
        self.assertEqual(len(active), 25)
        self.assertEqual({x.removeprefix(ACTIVE) for x in active},
                         set(APPROVED_WORKFLOWS))

    def test_all_four_staged_proposals_unapproved_and_byte_identical(self):
        manifest = source_manifest()
        self.assertEqual(manifest["original_approved_workflow_count"], 25)
        self.assertEqual(manifest["status"],
                         "SOURCE_STAGED_NONEXECUTABLE_PENDING_INDEPENDENT_SECURITY_REVIEW")
        self.assertIs(manifest["independent_security_review"], False)
        self.assertIs(manifest["owner_authorized_activation"], False)
        self.assertIs(manifest["mathematical_acceptance"], False)
        self.assertIs(manifest["release_authorized"], False)
        rows = manifest["proposals"]
        self.assertEqual(len(rows), 4)
        self.assertEqual(len({r["workflow_path"] for r in rows}), 4)
        self.assertEqual({Path(r["workflow_path"]).name for r in rows}, {
            "pr113-historical-migration-candidates.yml",
            "pr113-original-positive-controls-candidate.yml",
            "pr113-postseal-replay.yml",
            "pr113-source-controls-v3_1.yml",
        })
        for row in rows:
            old = row["workflow_path"]
            staged = row["staged_source_path"]
            self.assertTrue(old.startswith(ACTIVE))
            self.assertTrue(staged.startswith("docs/operations/pr113_unapproved_workflows/"))
            self.assertEqual(Path(old).name, Path(staged).name)
            self.assertFalse((ROOT / old).exists(), old)
            self.assertTrue((ROOT / staged).is_file(), staged)
            self.assertEqual(git("rev-parse", "HEAD:" + staged),
                             row["git_blob_oid"])
            self.assertIs(row["approved"], False)
            self.assertIs(row["installed"], False)
            self.assertIs(
                row["source_unchanged"],
                Path(old).name != "pr113-source-controls-v3_1.yml")

    def test_unreviewed_manifest_cannot_assert_success(self):
        record = source_manifest()
        self.assertNotIn("APPROVED", record["status"])
        for field in ("independent_security_review",
                      "owner_authorized_activation",
                      "mathematical_acceptance", "release_authorized"):
            self.assertIs(record[field], False)


    def test_full_v31_proposal_has_real_three_job_families_but_is_inactive(self):
        path = PROPOSALS / "pr113-source-controls-v3_1.yml"
        source = path.read_text(encoding="utf-8")
        self.assertIn("original-positive45:", source)
        self.assertIn("original-legacy20:", source)
        self.assertIn("claim-true-false11:", source)
        self.assertIn("research/final-mathematical-closure", source)
        self.assertIn("reviewed_claim11_false_sources", source)
        self.assertIn("reviewed_legacy20_selection_v31.json", source)
        self.assertFalse((ROOT / ACTIVE /
                          "pr113-source-controls-v3_1.yml").exists())


if __name__ == "__main__":
    unittest.main()
