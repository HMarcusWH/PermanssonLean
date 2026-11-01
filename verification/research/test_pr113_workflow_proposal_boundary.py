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


def owner_added():
    # Owner-approved added workflows (archive successor policy v2, at exactly
    # their approved blobs) are outside both PR113 profiles.
    from pr113_tooling_migration import owner_added_workflow_names
    return {ACTIVE+name for name in owner_added_workflow_names(ROOT)}


def active30():
    sources=[name for name in git("ls-tree","-r","--name-only","HEAD","--",
                                  ".github/workflows").splitlines()
             if name.startswith(ACTIVE) and name.endswith((".yml",".yaml"))
             and name not in owner_added()]
    if len(sources)==25:
        return None
    if len(sources)!=30:
        raise AssertionError("unexpected workflow profile inventory")
    from pr113_workflow_profile_v2 import audit
    return audit(ROOT,git("rev-parse","HEAD"),phase="active")


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
        profile=active30()
        if profile is not None:
            self.assertEqual(profile["historical_original_workflow_count"],25)
            self.assertEqual(profile["current_reviewed_workflow_count"],30)
            self.assertEqual(profile["retained_historical_count"],23)
            self.assertFalse(profile["independent_security_review"])
            return
        from verification.integrity.workflow_contract import APPROVED_WORKFLOWS
        added = owner_added()
        active = [x for x in git("ls-tree", "-r", "--name-only", "HEAD",
                                  "--", ".github/workflows").splitlines()
                  if x.startswith(ACTIVE) and x not in added]
        self.assertEqual(len(active), 25)
        self.assertEqual({x.removeprefix(ACTIVE) for x in active} |
                         {x.removeprefix(ACTIVE) for x in added},
                         set(APPROVED_WORKFLOWS))

    def test_all_five_staged_proposals_unapproved_and_byte_identical(self):
        manifest = source_manifest()
        self.assertEqual(manifest["original_approved_workflow_count"], 25)
        profile=active30()
        if profile is None:
            self.assertEqual(manifest["status"],
                             "SOURCE_STAGED_NONEXECUTABLE_PENDING_INDEPENDENT_SECURITY_REVIEW")
        self.assertIs(manifest["independent_security_review"], False)
        self.assertIs(manifest["owner_authorized_activation"], False)
        self.assertIs(manifest["mathematical_acceptance"], False)
        self.assertIs(manifest["release_authorized"], False)
        rows = manifest["proposals"]
        self.assertEqual(len(rows), 5)
        self.assertEqual(len({r["workflow_path"] for r in rows}), 5)
        self.assertEqual({Path(r["workflow_path"]).name for r in rows}, {
            "pr113-historical-migration-candidates.yml",
            "pr113-original-positive-controls-candidate.yml",
            "pr113-postseal-replay.yml",
            "pr113-source-controls-v3_1.yml",
            "pr113-preseal-fullscope.yml",
        })
        for row in rows:
            old = row["workflow_path"]
            staged = row["staged_source_path"]
            self.assertTrue(old.startswith(ACTIVE))
            self.assertTrue(staged.startswith("docs/operations/pr113_unapproved_workflows/"))
            self.assertEqual(Path(old).name, Path(staged).name)
            if profile is None:
                self.assertFalse((ROOT / old).exists(), old)
            else:
                self.assertTrue((ROOT / old).is_file(), old)
                self.assertEqual(git("rev-parse","HEAD:"+old),
                                 row["git_blob_oid"])
            self.assertTrue((ROOT / staged).is_file(), staged)
            self.assertEqual(git("rev-parse", "HEAD:" + staged),
                             row["git_blob_oid"])
            self.assertIs(row["approved"], False)
            self.assertIs(row["installed"], False)
            # Changed since baseline: v3.1 controls, and postseal for the
            # upstream preseal producer success check (P1-13).
            self.assertIs(
                row["source_unchanged"],
                Path(old).name not in ("pr113-source-controls-v3_1.yml",
                                       "pr113-postseal-replay.yml",
                                       "pr113-preseal-fullscope.yml",
                                       "pr113-historical-migration-candidates.yml"))

    def test_unreviewed_manifest_cannot_assert_success(self):
        record = source_manifest()
        self.assertNotIn("APPROVED", record["status"])
        for field in ("independent_security_review",
                      "owner_authorized_activation",
                      "mathematical_acceptance", "release_authorized"):
            self.assertIs(record[field], False)


    def test_fullscope_preseal_is_staged_and_matches_postseal_contract(self):
        from verification.research.final_closure_postseal_auth import (
            UPSTREAM_WORKFLOW, UPSTREAM_JOB, UPSTREAM_ARTIFACT)
        self.assertEqual(
            UPSTREAM_WORKFLOW,
            ".github/workflows/pr113-preseal-fullscope.yml")
        self.assertEqual(UPSTREAM_JOB, "preseal-fullscope-candidate")
        self.assertEqual(UPSTREAM_ARTIFACT,
                         "pr113-preseal-fullscope-candidate")
        proposed = PROPOSALS / "pr113-preseal-fullscope.yml"
        self.assertTrue(proposed.is_file())
        src = proposed.read_text(encoding="utf-8")
        for critical in (
            "preseal-fullscope-candidate:",
            "pr113-preseal-fullscope-candidate",
            "seal_approved.py",
            "--full",
            "pr113_preseal_input_carrier.py",
            "postseal_replay.py",
        ):
            self.assertIn(critical, src)
        installed=ROOT / ACTIVE / "pr113-preseal-fullscope.yml"
        if active30() is None:
            self.assertFalse(installed.exists())
        else:
            self.assertTrue(installed.is_file())
            self.assertEqual(git("rev-parse","HEAD:"+ACTIVE+
                                 "pr113-preseal-fullscope.yml"),
                             git("rev-parse","HEAD:docs/operations/"+
                                 "pr113_unapproved_workflows/pr113-preseal-fullscope.yml"))

    def test_full_v31_proposal_has_real_three_job_families_but_is_inactive(self):
        path = PROPOSALS / "pr113-source-controls-v3_1.yml"
        source = path.read_text(encoding="utf-8")
        self.assertIn("original-positive45:", source)
        self.assertIn("original-legacy20:", source)
        self.assertIn("claim-true-false11:", source)
        self.assertIn("research/final-mathematical-closure", source)
        self.assertIn("reviewed_claim11_false_sources", source)
        self.assertIn("legacy20_source_intent_v31.json", source)
        self.assertIn("pr113_original21_live_catalog.py", source)
        self.assertIn("pr113_legacy20_runtime_resolution.py", source)
        self.assertIn("reviewed_legacy20_runtime_event_choices.json", source)
        self.assertNotIn("reviewed_original21_catalog_v31.json", source)
        installed=ROOT / ACTIVE / "pr113-source-controls-v3_1.yml"
        if active30() is None:
            self.assertFalse(installed.exists())
        else:
            self.assertTrue(installed.is_file())
            self.assertEqual(git("rev-parse","HEAD:"+ACTIVE+
                                 "pr113-source-controls-v3_1.yml"),
                             git("rev-parse","HEAD:docs/operations/"+
                                 "pr113_unapproved_workflows/pr113-source-controls-v3_1.yml"))
        # The observer must exit successfully and store the real survey.
        # A separate explicit, independently reviewed resume consumes it.
        self.assertIn("original-legacy20-replay:", source)
        self.assertIn("if: github.event_name == 'workflow_dispatch'", source)
        self.assertIn("pr113_legacy20_choice_delivery.py", source)
        self.assertIn("survey_artifact_id:", source)
        self.assertIn("review_comment_id:", source)
        observer = source.split("  original-legacy20:", 1)[1].split(
            "  original-legacy20-replay:", 1)[0]
        self.assertNotIn("test -s \"$RUNNER_TEMP/reviewed_legacy20_runtime_event_choices.json\"",
                         observer)
        self.assertIn("pr113-v31-legacy20-observation-candidates", observer)
        self.assertIn("Retain observed actual events", observer)
        self.assertIn("reviewed_legacy20_runtime_event_choices.json",
                      source.split("  original-legacy20-replay:", 1)[1])



if __name__ == "__main__":
    unittest.main()
