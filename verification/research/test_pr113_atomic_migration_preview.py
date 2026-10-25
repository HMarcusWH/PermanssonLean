"""Review 23 unchanged originals, exact two replacements, five additions."""
import json
from pathlib import Path
import unittest
from unittest import mock

import pr113_atomic_migration_preview as preview

def fake_source():
    ROOT=Path(__file__).resolve().parents[2]
    head=preview.git("rev-parse","HEAD")
    return head,ROOT

class AtomicMigrationPreviewTests(unittest.TestCase):
    def test_real_source_preview_is_honestly_unapproved(self):
        H,root=fake_source()
        actual=preview.preview(H)
        self.assertEqual(actual["proposed_total_workflows"],30)
        self.assertEqual(actual["historical_preserved_workflows"],23)
        self.assertEqual(actual["review_pending_mandatory_replacements"],2)
        self.assertEqual(actual["review_pending_additional_workflows"],5)
        self.assertEqual(len(actual["virtual_source_members"]),30)
        self.assertEqual(len(actual["additional_original_test_replacements"]),2)
        self.assertRegex(actual["virtual_profile_sha256"],"^[a-f0-9]{64}$")
        for field in (
            "independent_security_review","owner_activation_authorized",
            "merge_authorized","mathematical_acceptance",
            "publication_authorized","active_workflow_set_modified"):
            self.assertIs(actual[field],False)

    def test_forged_head_or_staged_yaml_modification_is_rejected(self):
        H,_=fake_source()
        with self.assertRaises(preview.TransitionError):
            preview.preview("f"*40)
        original_git=preview.git
        target="docs/operations/pr113_required_gate_replacement_unapproved/research_lean_full.yml"
        def mutated(*args):
            if args==("show",H+":"+target):
                return original_git(*args)+"\n# unauthorized modification\n"
            return original_git(*args)
        with self.assertRaises(preview.TransitionError):
            preview.preview(H,git=mutated)

    def test_missing_source_or_invalid_old_profile_rejected(self):
        H,_=fake_source()
        def damaged(h):
            return {"status":"CANDIDATE","original_workflow_count":25}
        with self.assertRaises(preview.TransitionError):
            preview.preview(H,old_audit=damaged)


if __name__=="__main__":
    unittest.main()
