"""Adversarial byte/source-contract tests for the unreviewed case runner.

No test uses a mocked compiler result as a mathematical proof. The mock only
checks I/O, allowlists and anti-forgery contract behavior.
"""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import final_closure_original_semantic_batch as batch

H = "a" * 40


class FrozenOriginalCaseMutations(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="perm-case-source-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "synthetic-repository"
        self.root.mkdir()
        src = batch.SPECS["F-03"]
        self.source_path = self.root / src["source"]
        self.source_path.parent.mkdir(parents=True)
        self.source_path.write_bytes(
            b"import Mathlib.Tactic\n\nnamespace Fixture\n"
            b"theorem genuine : True := by trivial\nend Fixture\n"
        )
        test = self.root / src["test_path"]
        test.parent.mkdir(parents=True)
        test.write_text(
            "def test_false_feasible_anchor_with_conflicting_own_fibre_rejected():\n"
            "    pass\n"
        )
        mapping = self.root / "research/paper_closures/post_merge_112"
        mapping.mkdir(parents=True)
        row = {
            "case_id": "F-03", "effective_accepted": False,
            "test_method_candidates": [{
                "path": src["test_path"], "method": src["method"],
                "role": "SEMANTIC_NEGATIVE",
                "status": "DISCOVERED_UNREVIEWED_NOT_EXECUTION_EVIDENCE",
            }],
        }
        rows = [row] + [
            {"case_id": f"T-{i:02}", "effective_accepted": False,
             "test_method_candidates": []}
            for i in range(44)
        ]
        self.map = {"original_cases": 45, "cases": rows}
        self.map_path = mapping / "acceptance_case_source_map.json"
        self.save()

    def save(self):
        self.map_path.write_text(json.dumps(self.map))

    def test_original_source_bytes_are_preserved_and_no_import_was_added(self):
        entry, mutant = batch.frozen_spec("F-03", root=self.root)
        original = self.source_path.read_bytes()
        self.assertEqual(entry["source"], batch.SPECS["F-03"]["source"])
        self.assertTrue(mutant.startswith(original))
        self.assertNotEqual(mutant, original)
        self.assertEqual(mutant.count(b"import "), original.count(b"import "))
        self.assertIn(b"no_feasible_original_strict_anchor", mutant)
        self.assertNotIn(b"\nsorry", mutant)
        self.assertNotIn(b"\naxiom", mutant)

    def test_wrong_method_role_or_original_id_fails_closed(self):
        original = copy.deepcopy(self.map)
        for mutation in ("wrong_role", "wrong_name", "no_case",
                         "pretend_approved", "wrong_total"):
            self.map = copy.deepcopy(original)
            if mutation == "wrong_role":
                self.map["cases"][0]["test_method_candidates"][0]["role"] = "SCOPE_BOUNDARY"
            elif mutation == "wrong_name":
                self.map["cases"][0]["test_method_candidates"][0]["method"] = "test_unrelated"
            elif mutation == "no_case":
                self.map["cases"][0]["case_id"] = "C-OTHER"
            elif mutation == "pretend_approved":
                self.map["cases"][0]["effective_accepted"] = True
            else:
                self.map["original_cases"] = 44
            self.save()
            with self.subTest(mutation=mutation), self.assertRaises(
                batch.MutationEvidenceError
            ):
                batch.frozen_spec("F-03", root=self.root)

    def test_source_symlink_and_unregistered_case_rejected(self):
        with self.assertRaises(batch.MutationEvidenceError):
            batch.frozen_spec("D-999", root=self.root)
        self.source_path.unlink()
        outside = Path(self.tmp.name) / "outside"
        outside.write_bytes(b"theorem unrelated : True := by trivial")
        self.source_path.symlink_to(outside)
        with self.assertRaises(batch.MutationEvidenceError):
            batch.frozen_spec("F-03", root=self.root)

    def test_missing_test_or_new_import_rejected(self):
        original = copy.deepcopy(batch.SPECS["F-03"])
        with mock.patch.dict(
            batch.SPECS["F-03"],
            {"body": "import Mathlib.Tactic\nexample : False := by trivial"},
        ):
            with self.assertRaises(batch.MutationEvidenceError):
                batch.frozen_spec("F-03", root=self.root)
        test = self.root / original["test_path"]
        test.unlink()
        with self.assertRaises(batch.MutationEvidenceError):
            batch.frozen_spec("F-03", root=self.root)

    def test_mock_runner_cannot_claim_ci_id_or_independent_review(self):
        output = Path(self.tmp.name) / "detached-output"
        entry = copy.deepcopy(batch.SPECS["F-03"])
        with mock.patch.object(batch, "git_head", return_value=H), \
             mock.patch.object(batch, "frozen_spec",
                               return_value=(entry, b"import A\nexample : False := by trivial")), \
             mock.patch.object(batch, "produce",
                               return_value={"check_run_id": None,
                                             "outcome": "REJECTED_SEMANTIC"}) as producer, \
             mock.patch.object(batch, "seal_logs", return_value="e" * 64) as seal:
            result = batch.run_one(H, "F-03", output)
        self.assertTrue(producer.called)
        self.assertTrue(seal.called)
        self.assertEqual(result["status"], "DETACHED_UNREVIEWED_UNATTRIBUTED")
        self.assertIsNone(result["ci_check_run_id"])
        self.assertFalse(result["independent_review"])
        self.assertFalse(result["full_mathematical_acceptance"])
        self.assertTrue(output.is_dir())
        with self.assertRaises(batch.MutationEvidenceError):
            batch.run_one("not-a-commit", "F-03", output)

    def test_all_thirteen_spec_ids_and_method_owners_are_distinct(self):
        self.assertEqual(
            set(batch.SPECS),
            {"F-03", "D-02", "D-03", "D-04", "D-05",
             "D-06", "Q-03", "Q-04", "E-05",
             "A-03", "C-01", "D-07", "E-01"},
        )
        seen = set()
        for cid, entry in batch.SPECS.items():
            marker = (entry["test_path"], entry["method"])
            self.assertNotIn(marker, seen)
            seen.add(marker)
            self.assertTrue(entry["source"].startswith("PermanssonResearch/"))
            self.assertEqual(Path(entry["source"]).suffix, ".lean")


if __name__ == "__main__":
    unittest.main()
