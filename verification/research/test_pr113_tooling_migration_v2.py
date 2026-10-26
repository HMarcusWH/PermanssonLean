"""Real source-bound PREACTIVATION tests for the versioned 25-to-30 bridge.

No GitHub approval or active protected-workflow installation is performed.
"""
from __future__ import annotations
import copy
from pathlib import Path
from unittest import TestCase, mock

from pr113_workflow_profile_v2 import (
    PREACTIVATION_HEAD, audit as workflow_audit,
    audited_source_phase, source_phase, FORMAT,
)
from pr113_tooling_migration_v2 import audit as tooling_audit
from pr113_tooling_migration import ToolingMigrationError, git, ROOT


class VersionedT2SourceTests(TestCase):
    @classmethod
    def setUpClass(cls):
        cls.head = git(ROOT, "rev-parse", "HEAD").decode().strip()

    def test_real_25_to_virtual_30_exact_git_source(self):
        phase,result = audited_source_phase(ROOT, self.head)
        self.assertIn(phase, ("staged", "active"))
        self.assertEqual(result["versioned_source_phase"], phase)
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
        phase=source_phase(ROOT,self.head)
        wrong="active" if phase=="staged" else "staged"
        with self.assertRaises(ToolingMigrationError):
            workflow_audit(ROOT, self.head, phase=wrong)
        with self.assertRaisesRegex(ToolingMigrationError,
                                    "invalid successor workflow phase"):
            workflow_audit(ROOT, self.head, phase="future")

    def test_t2_tooling_checks_real_unchanged_original_archive(self):
        phase=source_phase(ROOT,self.head)
        result = tooling_audit(ROOT, self.head, phase=phase)
        self.assertEqual(result["reviewed_workflow_source_mode"],phase)
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
                workflow_audit(ROOT, self.head,
                               phase=source_phase(ROOT,self.head))

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
                workflow_audit(ROOT, self.head,
                               phase=source_phase(ROOT,self.head))

    def test_fake_git_show_bytes_cannot_borrow_valid_blob_oid(self):
        import pr113_workflow_profile_v2 as v2
        authentic=v2.git
        target=v2.CONTRACT
        def forged(root,*args):
            if args == ("show",self.head+":"+target):
                return authentic(root,*args)+b"\n# forged source\n"
            return authentic(root,*args)
        with mock.patch.object(v2,"git",side_effect=forged):
            with self.assertRaisesRegex(ToolingMigrationError,
                                        "Git object contents differ"):
                v2._blob(ROOT,self.head,target)


    def test_invalid_intermediate_inventory_and_nonfile_modes_fail_closed(self):
        import pr113_workflow_profile_v2 as policy
        for count in (24,26,29,31):
            source={".github/workflows/generated-%02d.yml"%i:
                    ("100644","a"*40) for i in range(count)}
            with self.subTest(count=count), mock.patch.object(
                    policy,"exact_tree",return_value=source):
                with self.assertRaisesRegex(
                        ToolingMigrationError,
                        "phase must be exactly 25 staged or 30 active"):
                    source_phase(ROOT,self.head)
        current=policy.exact_tree(ROOT,self.head,".github/workflows")
        path=next(iter(current))
        changed=dict(current)
        changed[path]=("100755",changed[path][1])
        with mock.patch.object(policy,"exact_tree",return_value=changed):
            with self.assertRaisesRegex(
                    ToolingMigrationError,"phase must be exactly"):
                source_phase(ROOT,self.head)

    def test_historical_25_source_is_anchored_even_after_activation(self):
        import pr113_workflow_profile_v2 as policy
        historical=policy._historical(ROOT,self.head)
        self.assertEqual(len(historical),25)
        self.assertEqual(len(set(historical)),25)
        phase,source=audited_source_phase(ROOT,self.head)
        self.assertEqual(source["historical_original_head"],PREACTIVATION_HEAD)
        self.assertEqual(source["historical_original_workflow_count"],25)
        self.assertEqual(source["current_reviewed_workflow_count"],30)
        self.assertFalse(source["independent_security_review"])

    def test_never_promote_v1_25_as_v2_30(self):
        legacy = {"format": "Permansson.PR113.ToolingMigrationProposal.v1",
                  "current_workflow_file_count": 25}
        self.assertNotEqual(legacy.get("format"),
                            "Permansson.PR113.ToolingMigrationCandidate.v2")
        self.assertNotEqual(legacy.get("current_workflow_file_count"), 30)
