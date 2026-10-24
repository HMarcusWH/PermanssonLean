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
    selection = {
        "cases": [
            {"case_id": row["case_id"],
             "historical_proof_declarations": [{"name": "real_proof"}],
             "test_source_candidates": ["verification/research/test_selected.py"],
             "test_method_candidates": [{
                 "path": "verification/research/test_selected.py",
                 "method": "test_selected_original",
                 "role": "COMPILER_SOURCE",
                 "status": "DISCOVERED_UNREVIEWED_NOT_EXECUTION_EVIDENCE"
             }]}
            for row in cases
        ]
    }
    return result, {"cases": cases}, claims, selection


class FullScopeContractTests(unittest.TestCase):
    def test_fully_mocked_graph_passes_only_as_source_not_release(self):
        evidence, cases, claims, selection = valid_inputs()
        proof = full.require_full_source(evidence, cases, claims, selection)
        self.assertEqual(proof["effective_case_count"], 45)
        self.assertEqual(proof["effective_claim_count"], 11)
        self.assertTrue(proof["not_yet_release"])

    def test_44_cases_and_10_claims_each_reject(self):
        for what in ("cases", "claims", "counterfeit"):
            evidence, cases, claims, selection = valid_inputs()
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
                full.require_full_source(evidence, cases, claims, selection)

    def test_missing_case_specific_selection_never_full(self):
        evidence, cases, claims, selection = valid_inputs()
        selection["cases"][7]["test_source_candidates"] = []
        with self.assertRaises(EvidenceError):
            full.require_full_source(evidence, cases, claims, selection)

    def test_method_only_filename_or_forged_role_cannot_count(self):
        for fault in ("drop", "forged", "duplicate"):
            evidence, cases, claims, selection = valid_inputs()
            routes = selection["cases"][4]["test_method_candidates"]
            if fault == "drop":
                routes.clear()
            elif fault == "forged":
                routes[0]["role"] = "APPROVED"
            else:
                import copy
                routes.append(copy.deepcopy(routes[0]))
            with self.subTest(fault=fault), self.assertRaises(EvidenceError):
                full.require_full_source(evidence, cases, claims, selection)

    def test_labels_cannot_replace_full_exact_sets(self):
        evidence, cases, claims, selection = valid_inputs()
        evidence["accepted_case_count"] = 45
        evidence["effective_cases"] = {"C-01": "VERIFIED_SELECTED_SCOPE"}
        with self.assertRaises(EvidenceError):
            full.require_full_source(evidence, cases, claims, selection)
        evidence, cases, claims, selection = valid_inputs()
        claims[-1]["id"] = "EXTRA"
        with self.assertRaises(EvidenceError):
            full.require_full_source(evidence, cases, claims, selection)

    def test_full_release_conjunction_uses_authenticated_external_artifacts(self):
        evidence, cases, claims, selection = valid_inputs()
        pdf = "d"*64
        pages = {"page-1.png": "1"*64, "page-2.png": "2"*64}
        ids = sorted(full.ORIGINAL_CLAIMS)
        manifest = {
            "status": "APPROVED_SOURCE_BOUND",
            "source_commit_sha": "f"*40,
            "claims": ids, "approved_manuscript_claims": ids,
            "accepted_claim_receipts": [
                {"claim_id": cid, "receipt_sha256": "a"*64} for cid in ids],
            "pdf_sha256": pdf, "pdf_pages": pages, "pdf_page_count": 2,
            "empirical_identification_status": "NOT_ESTABLISHED",
            "scientific_limitations": ["No empirical GR/PR certificate"],
            "reproduction_evidence_sha256": "b"*64,
            "archive_evidence_sha256": "c"*64,
        }
        provenance = {
            "M": "f"*40,
            "scholarly_reviews": [
                {"pdf_sha256": pdf, "pages": pages, "claim_ids": ids}],
            "reproduction_evidence": {
                "status": "TWO_CLEAN_SOURCE_BUILDS",
                "source_commit_sha": "f"*40,
                "pdf_sha256": pdf, "artifact_sha256": "b"*64,
                "authenticated_ci_artifact": True},
            "archive_evidence": {
                "status": "COMPLETE_ARCHIVE_REPLAY",
                "source_commit_sha": "f"*40,
                "pdf_sha256": pdf, "artifact_sha256": "c"*64,
                "authenticated_ci_artifact": True},
        }
        # This is explicitly a synthetic contract graph. The real provenance
        # authenticator cannot yet issue these artifacts; no release is claimed.
        pre = full.require_preseal_release(
            evidence, cases, claims, selection, manifest, provenance)
        self.assertEqual(pre["status"], "POSTMERGE_PRESEAL_READY")
        self.assertTrue(pre["not_yet_release"])
        without_archive = dict(provenance, archive_evidence=None)
        self.assertEqual(full.require_preseal_release(
            evidence, cases, claims, selection, manifest,
            without_archive)["status"], "POSTMERGE_PRESEAL_READY")
        success = full.require_full_release(
            evidence, cases, claims, selection, manifest, provenance)
        self.assertEqual(success["status"],
                         "FULL_MATHEMATICAL_CLOSURE_RELEASE_READY")
        for defect in ("10claims", "44cases", "no_scholarly", "no_repro",
                       "no_archive", "wrong_pdf_count", "wrong_merged_m"):
            import copy
            e, m, p = copy.deepcopy(evidence), copy.deepcopy(manifest), copy.deepcopy(provenance)
            if defect == "10claims":
                e["effective_claims"].pop()
                e["accepted_claim_count"] = 10
            elif defect == "44cases":
                e["effective_cases"].pop("C-45")
                e["accepted_case_count"] = 44
                e["pending_case_count"] = 1
            elif defect == "no_scholarly":
                p["scholarly_reviews"] = []
            elif defect == "no_repro":
                p["reproduction_evidence"] = None
            elif defect == "no_archive":
                p["archive_evidence"] = None
            elif defect == "wrong_pdf_count":
                m["pdf_page_count"] = 1
            else:
                m["source_commit_sha"] = "e"*40
            with self.subTest(defect=defect), self.assertRaises(EvidenceError):
                full.require_full_release(e, cases, claims, selection, m, p)

    def test_premerge_full_gates_full_review_and_requires_no_future_M(self):
        evidence, cases, claims, selection = valid_inputs()
        receipt = {
            "format": gate.FORMAT_V3, "phase": "premerge_review",
            "merged_main_sha": None, "head_sha": "a"*40,
            "evidence_bundle_sha256": "b"*64,
        }
        provenance = {"H": "a"*40, "S": "c"*40,
                      "checks": {}, "review_scopes": {}}
        with mock.patch.object(gate, "require_complete_obligation_receipts",
                               return_value={"receipt_contract": "MOCK_ONLY"}), \
             mock.patch.object(gate, "validate_overlay"), \
             mock.patch.object(gate, "verify_premerge",
                               return_value=provenance), \
             mock.patch.object(gate, "load_detached_bundle",
                               return_value={}), \
             mock.patch.object(gate, "effective_acceptance",
                               return_value=evidence), \
             mock.patch.object(gate, "authenticate_all_76",
                               return_value={"status": "MOCK_ONLY_V31"}), \
             mock.patch.object(gate, "read_json",
                               side_effect=[cases, {"claims": claims}, selection, {"claims": []}]):
            status = gate.premerge(
                receipt, None, full=True,
                additional_contract="/mock/contract.json",
                additional_zips="/mock/producer-zips",
                workflow_blob_candidates="/mock/oid-candidates.json")
        self.assertEqual(status["gate"], "PREMERGE_FULL_SOURCE_READY")
        self.assertFalse(status["merge_authorized"])
        self.assertFalse(status["scientific_release_approved"])
        self.assertIsNone(status["merged_main_sha"])
        self.assertEqual(status["additional_execution"]["status"],
                         "MOCK_ONLY_V31")


if __name__ == "__main__":
    unittest.main()
