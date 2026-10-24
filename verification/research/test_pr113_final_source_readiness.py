"""Synthetic-only source coverage adversaries, not effective math acceptance."""
import copy
import unittest

import pr113_final_source_readiness as ready

CASE_IDS={f"C-{i:02d}" for i in range(1,46)}
CLAIM_IDS=sorted(ready.CLAIMS)

def fixture():
    proofs=[
        {"id":f"all:{i:04d}",
         "case_ids":[sorted(CASE_IDS)[i%45]],
         "claim_ids":[CLAIM_IDS[i%11]]}
        for i in range(259)]
    plus=[{"case_ids":[cid],"claim_ids":[]}
          for cid in sorted(CASE_IDS)[:25]]
    minus=[{"case_ids":[cid],"claim_ids":[]}
           for cid in sorted(CASE_IDS)[:25]]
    return {
        "format": "Permansson.FinalClosureDetachedReceipts.v3",
        "compiler_axiom_receipts":proofs,
        "producer_artifacts":[{"artifact_id":i} for i in range(1,22)],
        "positive_test_receipts":plus,
        "semantic_negative_receipts":minus,
    }

class ReadinessCoverageTests(unittest.TestCase):
    def test_missing_20_cases_and_all_claim_controls_block_acceptance(self):
        rows=fixture()
        result=ready.candidate_coverage(rows,CASE_IDS)
        self.assertEqual(result["source_proofs"],259)
        self.assertEqual(result["producer_shards"],21)
        self.assertEqual(result["cases_with_positive_negative_controls"],25)
        self.assertEqual(len(result["missing_original_case_controls"]),20)
        self.assertEqual(len(result["missing_new_claim_controls"]),11)
        self.assertFalse(result["candidate_controls_complete"])
        self.assertFalse(result["mathematical_release_approved"])

    def test_pretend_full_case_claim_controls_are_still_unreviewed(self):
        rows=fixture()
        for cid in sorted(CASE_IDS)[25:]:
            rows["positive_test_receipts"].append(
                {"case_ids":[cid],"claim_ids":[]})
            rows["semantic_negative_receipts"].append(
                {"case_ids":[cid],"claim_ids":[]})
        for claim in CLAIM_IDS:
            rows["positive_test_receipts"].append(
                {"case_ids":[],"claim_ids":[claim]})
            rows["semantic_negative_receipts"].append(
                {"case_ids":[],"claim_ids":[claim]})
        result=ready.candidate_coverage(rows,CASE_IDS)
        # A complete set of labels must NOT assert genuine test execution.
        self.assertTrue(result["label_coverage_only"])
        self.assertFalse(result["candidate_controls_complete"])
        self.assertEqual(result["producer_source_and_role_validation"],
                         "NOT_VALIDATED")
        self.assertEqual(result["independent_case_reviews"],0)
        self.assertEqual(result["independent_claim_reviews"],0)
        self.assertFalse(result["merge_authorized"])

    def test_source_declaration_or_producer_count_must_be_complete(self):
        rows=fixture()
        rows["compiler_axiom_receipts"].pop()
        with self.assertRaises(ready.ReadinessError):
            ready.candidate_coverage(rows,CASE_IDS)
        rows=fixture()
        rows["producer_artifacts"].pop()
        with self.assertRaises(ready.ReadinessError):
            ready.candidate_coverage(rows,CASE_IDS)
        rows=fixture()
        rows["positive_test_receipts"].append(
            {"case_ids":["INVENTED-CASE"],"claim_ids":[]})
        with self.assertRaises(ready.ReadinessError):
            ready.candidate_coverage(rows,CASE_IDS)
