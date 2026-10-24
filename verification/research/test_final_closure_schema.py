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

    def test_claim_only_receipts_validate_but_orphans_fail(self):
        x = candidate()
        base = {
            "id": "claim-only", "head_sha": H, "check_run_id": None,
            "test_path": "verification/research/test_demo.py",
            "test_name": "test_demo", "source_sha256": "1"*64,
            "case_ids": [], "claim_ids": ["N2"],
            "positive_control": {
                "compiled": True, "exit_code": 0, "lean_toolchain": "4.34.0",
                "log_member": "positive.log", "log_sha256": "2"*64,
            },
            "outcome": "PASS", "compiler_exit_code": 0,
            "log_member": "positive.log", "log_sha256": "2"*64,
        }
        x["positive_test_receipts"] = [base]
        schema.validate_overlay(x)
        orphan = copy.deepcopy(x)
        orphan["positive_test_receipts"][0]["claim_ids"] = []
        with self.assertRaises(EvidenceError):
            schema.validate_overlay(orphan)
        x["semantic_negative_receipts"] = [{
            **base, "id": "claim-only-negative", "outcome": "REJECTED_SEMANTIC",
            "compiler_exit_code": 1, "log_member": "negative.log",
            "mutant_source_member": "mutated.lean", "mutant_source_sha256": "3"*64,
            "original_lean_source_path": "Proof.lean",
            "original_lean_source_member": "original.lean",
            "original_lean_source_sha256": "4"*64,
        }]
        schema.validate_overlay(x)
        x["semantic_negative_receipts"][0]["claim_ids"] = []
        with self.assertRaises(EvidenceError):
            schema.validate_overlay(x)

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

    def test_v3_requires_true_producing_job_refs_and_all_21_entries(self):
        x = candidate()
        x["format"] = schema.FORMAT_V3
        x["producer_artifacts"] = []
        with self.assertRaises(EvidenceError):
            schema.validate_overlay(x)
        from final_closure_candidate_artifact_auth import KINDS
        records = []
        for kind, spec in KINDS.items():
            for shard in range(spec["count"]):
                k = len(records)+1
                records.append({
                    "format":"Permansson.PR113.AuthenticatedProducerArtifact.v1",
                    "status":"CI_ARTIFACT_DIGEST_VERIFIED_UNREVIEWED",
                    "head_sha": H,
                    "workflow_path":spec["workflow"],
                    "run_id":1000+k,"run_attempt":1,
                    "job_id":2000+k,"actual_check_run_id":3000+k,
                    "artifact_id":4000+k,
                    "artifact_name":spec["artifact"]+str(shard),
                    "artifact_sha256":"a"*64,"manifest_sha256":"b"*64,
                    "mathematical_acceptance":False,"independent_review":False,
                    "scientific_release_approved":False,
                    "merged_main_sha":None,
                    "evidence_zip_member":f"producer/{4000+k}.zip",
                })
        x["producer_artifacts"] = records
        schema.validate_overlay(x)  # STRUCTURAL ONLY; not real GH review
        x["producer_artifacts"][0]["actual_check_run_id"] = True
        with self.assertRaises(EvidenceError):
            schema.validate_overlay(x)
        x["producer_artifacts"][0]["actual_check_run_id"] = 3001
        x["producer_artifacts"][0]["mathematical_acceptance"] = True
        with self.assertRaises(EvidenceError):
            schema.validate_overlay(x)

    def test_unknown_schema_rule_fails_closed(self):
        with self.assertRaises(EvidenceError):
            schema._check_spec({"magicallyAccept": True})


if __name__ == "__main__":
    unittest.main()
