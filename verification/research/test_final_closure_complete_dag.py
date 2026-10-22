"""Adversarial exact 45/11 receipt DAG tests. Mock graph is NOT acceptance."""
import copy
import unittest

import final_closure_full_contract as full
from final_closure_case_receipts import EvidenceError


def mocked_graph():
    ids = [f"C-{n:02d}" for n in range(1, 46)]
    cases = []
    compiler = []
    positives, negatives = [], []
    decisions = []
    path = "verification/research/test_required.py"
    for idx, cid in enumerate(ids):
        p = f"proof-{cid}"
        d = f"Node.valid{idx}"
        pp = f"Proofs/{idx}.lean"
        cases.append({
            "case_id": cid,
            "historical_proof_declarations": [{"path": pp, "name": f"valid{idx}"}],
            "test_method_candidates": [
                {"path": path, "method": "test_positive", "role": "EXACT_CHECK"},
                {"path": path, "method": "test_false", "role": "SEMANTIC_NEGATIVE"},
            ],
            "new_claim_source_candidates": [],
        })
        compiler.append({"id": p, "path": pp, "declaration": d,
                         "case_ids": [cid], "claim_ids": []})
        positives.append({"id": f"positive-{cid}", "test_path": path,
                          "test_name": "test_positive", "case_ids": [cid]})
        negatives.append({"id": f"negative-{cid}", "test_path": path,
                          "test_name": "test_false", "case_ids": [cid]})
        decisions.append({"case_id": cid, "proof_ids": [p],
                          "positive_ids": [f"positive-{cid}"],
                          "negative_ids": [f"negative-{cid}"]})
    claims, claim_decisions = [], []
    for cid in sorted(full.ORIGINAL_CLAIMS):
        decls, refs = [], []
        for k in range(2 if cid == "Q1" else 1):
            proofid = f"{cid}:{k}"
            decl = f"ClaimScope.{cid}.support{k}"
            source = f"Claims/{cid}-{k}.lean"
            decls.append({"path": source, "declaration": decl})
            compiler.append({"id": proofid, "path": source,
                             "declaration": decl, "claim_ids": [cid],
                             "case_ids": []})
            refs.append(proofid)
        claims.append({"claim_id": cid, "declarations": decls})
        claim_decisions.append({"claim_id": cid, "proof_ids": refs})
    overlay = {
        "compiler_axiom_receipts": compiler,
        "positive_test_receipts": positives,
        "semantic_negative_receipts": negatives,
        "case_decisions": decisions,
        "claim_decisions": claim_decisions,
    }
    return overlay, {"cases": cases}, {"claims": claims}


class CompleteObligationReceiptTests(unittest.TestCase):
    def test_mock_complete_dag_is_only_structurally_covered(self):
        a, b, c = mocked_graph()
        result = full.require_complete_obligation_receipts(a, b, c)
        self.assertEqual(result["cases_covered"], 45)
        self.assertEqual(result["claims_covered"], 11)
        self.assertTrue(result["review_and_ci_still_required"])

    def test_one_of_two_required_claim_proofs_cannot_suffice(self):
        a, b, c = mocked_graph()
        row = next(r for r in a["claim_decisions"] if r["claim_id"] == "Q1")
        row["proof_ids"].pop()
        with self.assertRaisesRegex(EvidenceError, "omits supporting"):
            full.require_complete_obligation_receipts(a, b, c)

    def test_unrelated_proof_with_valid_case_label_does_not_cover_contract(self):
        a, b, c = mocked_graph()
        proof = next(p for p in a["compiler_axiom_receipts"]
                     if p["id"] == "proof-C-12")
        proof["path"] = "Other/Unrelated.lean"
        with self.assertRaisesRegex(EvidenceError, "missing original"):
            full.require_complete_obligation_receipts(a, b, c)

    def test_source_right_but_declaration_wrong_rejected(self):
        a, b, c = mocked_graph()
        proof = next(p for p in a["compiler_axiom_receipts"]
                     if p["id"] == "proof-C-07")
        proof["declaration"] = "Node.validDifferent"
        with self.assertRaises(EvidenceError):
            full.require_complete_obligation_receipts(a, b, c)

    def test_missing_wrong_role_and_forged_nonselected_method_rejected(self):
        for mode in ("wrongrole", "unselected", "borrowed"):
            a, b, c = mocked_graph()
            negative = next(n for n in a["semantic_negative_receipts"]
                            if n["id"] == "negative-C-05")
            if mode == "wrongrole":
                b["cases"][4]["test_method_candidates"][1]["role"] = "EXACT_CHECK"
            elif mode == "unselected":
                negative["test_name"] = "test_unrelated"
            else:
                negative["case_ids"] = ["C-06"]
            with self.subTest(mode=mode), self.assertRaises(EvidenceError):
                full.require_complete_obligation_receipts(a, b, c)

    def test_claim_cannot_borrow_one_proof_from_another_owner(self):
        a, b, c = mocked_graph()
        row = next(r for r in a["claim_decisions"] if r["claim_id"] == "M1")
        other = next(p for p in a["compiler_axiom_receipts"]
                     if p["id"] == "Q1:0")
        other["claim_ids"].append("M1")
        row["proof_ids"] = ["Q1:0"]
        with self.assertRaisesRegex(EvidenceError, "omits supporting"):
            full.require_complete_obligation_receipts(a, b, c)

    def test_unlisted_or_duplicate_case_or_claim_never_conjoins(self):
        for what in ("case", "claim", "duplicate"):
            a, b, c = mocked_graph()
            if what == "case":
                a["case_decisions"].pop()
            elif what == "claim":
                a["claim_decisions"].pop()
            else:
                a["compiler_axiom_receipts"].append(
                    copy.deepcopy(a["compiler_axiom_receipts"][0]))
            with self.subTest(what=what), self.assertRaises(EvidenceError):
                full.require_complete_obligation_receipts(a, b, c)

    def test_case_link_to_new_claim_source_is_required(self):
        a, b, c = mocked_graph()
        b["cases"][0]["new_claim_source_candidates"] = [
            {"id": "Q1", "path": "Claims/Q1-0.lean"}
        ]
        with self.assertRaises(EvidenceError):
            full.require_complete_obligation_receipts(a, b, c)


if __name__ == "__main__":
    unittest.main()
