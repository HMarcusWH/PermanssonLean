"""Full selected-source gates use mocked effective decisions, not live approvals."""
import copy
import unittest
from unittest import mock

import final_closure_full_contract as full
import final_closure_gate as gate
from final_closure_case_receipts import EvidenceError


def valid_inputs():
    cases = [{"case_id": f"C-{i:02d}"} for i in range(1, 46)]
    claims = [{"id": cid} for cid in sorted(full.ORIGINAL_CLAIMS)]
    result = {
        "effective_cases": {c["case_id"]: "VERIFIED_SELECTED_SCOPE"
                            for c in cases},
        "effective_claims": sorted(full.ORIGINAL_CLAIMS),
        "accepted_case_count": 45, "pending_case_count": 0,
        "accepted_claim_count": 11,
    }
    return result, {"cases": cases}, claims


class FullScopeContractTests(unittest.TestCase):
    def test_fully_mocked_graph_passes_only_as_source_not_release(self):
        evidence, cases, claims = valid_inputs()
        proof = full.require_full_source(evidence, cases, claims)
        self.assertEqual(proof["effective_case_count"], 45)
        self.assertEqual(proof["effective_claim_count"], 11)
        self.assertTrue(proof["not_yet_release"])

    def test_44_cases_and_10_claims_each_reject(self):
        for what in ("cases", "claims", "counterfeit"):
            evidence, cases, claims = valid_inputs()
            if what == "cases":
                evidence["effective_cases"].pop("C-45")
                evidence["accepted_case_count"] = 44
                evidence["pending_case_count"] = 1
            elif what == "claims":
                evidence["effective_claims"].remove("Q3")
                evidence["accepted_claim_count"] = 10
            else:
                evidence["effective_claims"][-1] = "FAKE"
            with self.subTest(what=what), self.assertRaises(EvidenceError):
                full.require_full_source(evidence, cases, claims)

    def test_labels_cannot_replace_full_exact_sets(self):
        evidence, cases, claims = valid_inputs()
        evidence["accepted_case_count"] = 45
        evidence["effective_cases"] = {"C-01": "VERIFIED_SELECTED_SCOPE"}
        with self.assertRaises(EvidenceError):
            full.require_full_source(evidence, cases, claims)
        evidence, cases, claims = valid_inputs()
        claims[-1]["id"] = "EXTRA"
        with self.assertRaises(EvidenceError):
            full.require_full_source(evidence, cases, claims)

    def test_premerge_full_gates_full_review_and_requires_no_future_M(self):
        evidence, cases, claims = valid_inputs()
        receipt = {
            "format": gate.FORMAT, "phase": "premerge_review",
            "merged_main_sha": None, "head_sha": "a"*40,
            "evidence_bundle_sha256": "b"*64,
        }
        provenance = {"H": "a"*40, "S": "c"*40,
                      "checks": {}, "review_scopes": {}}
        with mock.patch.object(gate, "validate_overlay"), \
             mock.patch.object(gate, "verify_premerge",
                               return_value=provenance), \
             mock.patch.object(gate, "load_detached_bundle",
                               return_value={}), \
             mock.patch.object(gate, "effective_acceptance",
                               return_value=evidence), \
             mock.patch.object(gate, "read_json",
                               side_effect=[cases, {"claims": claims}]):
            status = gate.premerge(receipt, None, full=True)
        self.assertEqual(status["gate"], "PREMERGE_FULL_SOURCE_READY")
        self.assertFalse(status["merge_authorized"])
        self.assertFalse(status["scientific_release_approved"])
        self.assertIsNone(status["merged_main_sha"])


if __name__ == "__main__":
    unittest.main()
