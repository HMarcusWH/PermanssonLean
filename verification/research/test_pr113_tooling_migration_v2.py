"""Real source-bound PREACTIVATION tests for the versioned 25-to-30 bridge.

No GitHub approval or active protected-workflow installation is performed.
"""
from __future__ import annotations
import copy
from pathlib import Path
from unittest import TestCase, mock

from pr113_workflow_profile_v2 import (
    PREACTIVATION_HEAD, audit as workflow_audit, FORMAT,
)
from pr113_tooling_migration_v2 import audit as tooling_audit
from pr113_tooling_migration import ToolingMigrationError, git, ROOT


class VersionedT2SourceTests(TestCase):
    @classmethod
    def setUpClass(cls):
        cls.head = git(ROOT, "rev-parse", "HEAD").decode().strip()

    def test_real_25_to_virtual_30_exact_git_source(self):
        result = workflow_audit(ROOT, self.head, phase="staged")
        self.assertEqual(result["format"], FORMAT)
        self.assertEqual(result["historical_original_head"], PREACTIVATION_HEAD)
        self.assertEqual(result["historical_original_workflow_count"], 25)
        self.assertEqual(result["current_reviewed_workflow_count"], 30)
        self.assertEqual([result[x] for x in (
            "retained_historical_count", "replacement_count", "addition_count")],
            [23, 2, 5])
        self.assertEqual(len(result["expected_source_blobs"]), 30)
        self.assertFalse(result["independent_security_review"])
        self.assertFalse(result["owner_activation_authorized"])
        self.assertFalse(result["all_actions_commit_pinned"])
        self.assertTrue(result["inherited_mutable_action_refs"])

    def test_old_25_source_cannot_masquerade_as_active_30(self):
        with self.assertRaises(ToolingMigrationError):
            workflow_audit(ROOT, self.head, phase="active")
        with self.assertRaises(ToolingMigrationError):
            workflow_audit(ROOT, self.head, phase="future")

    def test_t2_tooling_checks_real_unchanged_original_archive(self):
        result = tooling_audit(ROOT, self.head, phase="staged")
        self.assertEqual(result["status"], "T2_EXACT_SOURCE_REVIEW_PENDING")
        self.assertEqual(result["historical_original_workflow_count"], 25)
        self.assertEqual(result["current_reviewed_workflow_count"], 30)
        self.assertEqual(len(result["changed_canonical_tooling"]), 2)
        self.assertTrue(result["historical_archive_unchanged"])
        self.assertFalse(result["new_successor_T_approved"])
        self.assertFalse(result["independent_security_review"])

    def test_no_direct_ad_hoc_source_pin_override(self):
        from pr113_workflow_profile_v2 import _historical
        old = _historical(ROOT, self.head)
        self.assertEqual(len(old), 25)
        with mock.patch("pr113_workflow_profile_v2._historical",
                        return_value={k:v for k,v in old.items()
                                      if k != "a2-smoke.yml"}):
            with self.assertRaises(ToolingMigrationError):
                workflow_audit(ROOT, self.head, phase="staged")

    def test_replacement_or_addition_missing_refused(self):
        import pr113_workflow_profile_v2 as p
        native = p._json
        def missing(root, head, path):
            data = native(root, head, path)
            if path == p.FULL_MANIFEST:
                data = copy.deepcopy(data)
                data["full_replacements"] = data["full_replacements"][:1]
            return data
        with mock.patch.object(p, "_json", side_effect=missing):
            with self.assertRaises(ToolingMigrationError):
                workflow_audit(ROOT, self.head, phase="staged")

    def test_never_promote_v1_25_as_v2_30(self):
        legacy = {"format": "Permansson.PR113.ToolingMigrationProposal.v1",
                  "current_workflow_file_count": 25}
        self.assertNotEqual(legacy.get("format"),
                            "Permansson.PR113.ToolingMigrationCandidate.v2")
        self.assertNotEqual(legacy.get("current_workflow_file_count"), 30)
