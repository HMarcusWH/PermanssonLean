"""Detached receipt schema adversaries. All successful inputs are mock candidates."""
import copy
import unittest

import final_closure_schema as schema
from final_closure_case_receipts import EvidenceError

H = "a" * 40


def candidate():
    return {
        "format": "Permansson.FinalClosureDetachedReceipts.v2",
        "phase": "premerge_review", "base_sha": "b"*40,
        "head_sha": H, "synthetic_sha": "c"*40,
        "merged_main_sha": None, "evidence_bundle_sha256": "d"*64,
        "source_bound_ci": [
            {"name": f"check{i}", "id": i + 1, "head_sha": H}
            for i in range(7)
        ],
        "compiler_axiom_receipts": [], "positive_test_receipts": [],
        "semantic_negative_receipts": [], "case_decisions": [],
        "claim_decisions": [], "independent_source_reviews": [],
        "trusted_axioms": ["Classical.choice", "Quot.sound", "propext"],
    }


class SchemaBoundaryTests(unittest.TestCase):
    def test_premerge_candidate_is_valid_but_not_approved(self):
        x = candidate()
        self.assertIs(schema.validate_overlay(x), x)
        self.assertEqual(x["claim_decisions"], [])
        self.assertEqual(x["case_decisions"], [])

    def test_unknown_property_and_boolean_ci_id_rejected(self):
        x = candidate()
        x["surprise"] = "yes"
        with self.assertRaises(EvidenceError):
            schema.validate_overlay(x)
        x = candidate()
        x["source_bound_ci"][0]["id"] = True
        with self.assertRaises(EvidenceError):
            schema.validate_overlay(x)

    def test_phase_requires_matching_merged_SHA_and_bound_receipts(self):
        x = candidate()
        x["merged_main_sha"] = "f"*40
        with self.assertRaises(EvidenceError):
            schema.validate_overlay(x)
        x["phase"] = "postmerge_acceptance"
        schema.validate_overlay(x)
        x["merged_main_sha"] = None
        with self.assertRaises(EvidenceError):
            schema.validate_overlay(x)

    def test_test_receipts_allow_claim_ids_but_not_unknown_data(self):
        x = candidate()
        test = {
            "id": "negative:1", "head_sha": H, "check_run_id": None,
            "test_path": "verification/research/test_demo.py",
            "test_name": "test_demo", "source_sha256": "1"*64,
            "case_ids": ["Q-05"], "claim_ids": ["Q1"],
            "positive_control": {
                "compiled": True, "exit_code": 0,
                "lean_toolchain": "4.34.0",
                "log_member": "pos.log", "log_sha256": "2"*64,
            },
            "outcome": "PASS", "compiler_exit_code": 0,
            "log_member": "pos.log", "log_sha256": "2"*64,
        }
        x["positive_test_receipts"] = [test]
        schema.validate_overlay(x)
        x["semantic_negative_receipts"] = [{
            **test, "id": "negative:2", "outcome": "REJECTED_SEMANTIC",
            "compiler_exit_code": 1,
            "log_member": "neg.log",
            "mutant_source_member": "mut.lean",
            "mutant_source_sha256": "3"*64,
            "original_lean_source_path": "Demo.lean",
            "original_lean_source_sha256": "4"*64,
            "original_lean_source_member": "original.lean",
        }]
        schema.validate_overlay(x)
        bad = copy.deepcopy(x)
        bad["semantic_negative_receipts"][0]["unexpected"] = True
        with self.assertRaises(EvidenceError):
            schema.validate_overlay(bad)
        x["phase"] = "postmerge_acceptance"
        x["merged_main_sha"] = "e"*40
        with self.assertRaises(EvidenceError):
            schema.validate_overlay(x)  # no attributable execution check

    def test_claim_decision_requires_positive_and_negative_receipts(self):
        decision = {"id": "claim-1", "claim_id": "Q1",
                    "proof_ids": ["proof"], "positive_ids": ["pos"],
                    "negative_ids": ["neg"], "review_id": 11}
        good = candidate()
        good["claim_decisions"] = [decision]
        schema.validate_overlay(good)  # Shape only, not real approval.
        for key in ("positive_ids", "negative_ids"):
            missing = copy.deepcopy(good)
            del missing["claim_decisions"][0][key]
            with self.subTest(key=key), self.assertRaises(EvidenceError):
                schema.validate_overlay(missing)
            empty = copy.deepcopy(good)
            empty["claim_decisions"][0][key] = []
            with self.subTest(key=key + " empty"), self.assertRaises(EvidenceError):
                schema.validate_overlay(empty)

    def test_unknown_schema_rule_fails_closed(self):
        with self.assertRaises(EvidenceError):
            schema._check_spec({"magicallyAccept": True})


if __name__ == "__main__":
    unittest.main()
