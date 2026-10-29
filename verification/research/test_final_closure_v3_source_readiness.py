"""Role/owner correctness tests. Mock rows are NOT compiler/reviewer evidence."""
import copy
import unittest

import final_closure_v3_source_readiness as gate

CASEIDS=[f"C-{i:02d}" for i in range(1,46)]
CLAIMS=sorted(gate.CLAIMS)

def fixture():
    cases,proofs,plus,minus=[],[],[],[]
    for n,cid in enumerate(CASEIDS):
        qualified=f"Test.Valid.theorem_{n}"
        path=f"Proofs/Case_{n}.lean"
        pos=f"test_positive_{n}"
        neg=f"test_semantic_negative_{n}"
        tpos=f"verification/research/test_source_{n}.py"
        tneg=f"verification/research/test_negative_{n}.py"
        cases.append({
            "case_id":cid,
            "historical_proof_declarations":[{"path":path,"name":qualified}],
            "new_claim_source_candidates":[],
            "test_method_candidates":[
                {"path":tpos,"method":pos,"role":"EXACT_CHECK"},
                {"path":tneg,"method":neg,"role":"SEMANTIC_NEGATIVE"},
            ],
        })
        proofs.append({"id":f"case:{n}","path":path,"declaration":qualified,
                       "case_ids":[cid],"claim_ids":[]})
        plus.append({"id":f"pos:{n}","test_path":tpos,"test_name":pos,
                     "case_ids":[cid],"claim_ids":[]})
        minus.append({"id":f"neg:{n}","test_path":tneg,"test_name":neg,
                      "case_ids":[cid],"claim_ids":[]})
    claim_rows=[]
    for n,cid in enumerate(CLAIMS):
        path=f"Proofs/Claim_{n}.lean";qualified=f"Claim.Valid.statement_{n}"
        t=f"verification/research/test_claim_{n}.py"
        claim_rows.append({"claim_id":cid,
                           "declarations":[{"path":path,"declaration":qualified}],
                           "test_source_candidates":[t]})
        proofs.append({"id":f"claim:{n}","path":path,
                       "declaration":qualified,"case_ids":[],
                       "claim_ids":[cid]})
        plus.append({"id":f"claim-positive:{n}","test_path":t,
                     "test_name":f"test_claim_positive_{n}",
                     "case_ids":[],"claim_ids":[cid]})
        minus.append({"id":f"claim-negative:{n}","test_path":t,
                      "test_name":f"test_claim_false_{n}",
                      "case_ids":[],"claim_ids":[cid]})
    for n in range(259-len(proofs)):
        proofs.append({"id":f"extra:{n}","path":"Proofs/Other.lean",
                       "declaration":f"Other.theorem_{n}",
                       "case_ids":[], "claim_ids":[]})
    return (
        {"compiler_axiom_receipts":proofs,
         "positive_test_receipts":plus,
         "semantic_negative_receipts":minus},
        {"cases":cases},{"claims":claim_rows},
    )

class ExactOriginalRoleTests(unittest.TestCase):
    def test_complete_synthetic_scope_still_is_unreviewed(self):
        over,cases,claims=fixture()
        report=gate.route_coverage(over,cases,claims)
        self.assertEqual(report["cases_with_admissible_positive"],45)
        self.assertEqual(report["cases_with_admissible_negative"],45)
        self.assertEqual(report["claims_with_source_selected_positive"],11)
        self.assertEqual(report["claims_with_source_selected_negative"],11)
        self.assertTrue(report["all_original_roles_and_claim_sources_complete"])
        self.assertFalse(report["independent_review"])
        self.assertFalse(report["mathematical_release_approved"])

    def test_negative_role_positive_log_is_not_admissible_positive(self):
        over,cases,claims=fixture()
        over["positive_test_receipts"][0]["test_path"] = (
            over["semantic_negative_receipts"][0]["test_path"])
        over["positive_test_receipts"][0]["test_name"] = (
            over["semantic_negative_receipts"][0]["test_name"])
        report=gate.route_coverage(over,cases,claims)
        self.assertIn(CASEIDS[0], report["missing_original_positive"])
        self.assertIn(CASEIDS[0], report["inadmissible_original_method_roles"])
        self.assertFalse(report["all_original_roles_and_claim_sources_complete"])

    def test_one_valid_route_cannot_hide_an_ineligible_extra(self):
        over,cases,claims=fixture()
        alien=dict(over["positive_test_receipts"][0])
        alien["id"]="alien-positive"
        alien["test_path"]=over["semantic_negative_receipts"][0]["test_path"]
        alien["test_name"]=over["semantic_negative_receipts"][0]["test_name"]
        over["positive_test_receipts"].append(alien)
        result=gate.route_coverage(over,cases,claims)
        self.assertIn(CASEIDS[0],result["inadmissible_original_method_roles"])
        self.assertFalse(result["all_original_roles_and_claim_sources_complete"])
        over,cases,claims=fixture()
        alien=dict(over["positive_test_receipts"][-1])
        alien["id"]="alien-claim-positive"
        alien["test_path"]="verification/research/test_unrelated_claim.py"
        over["positive_test_receipts"].append(alien)
        result=gate.route_coverage(over,cases,claims)
        self.assertIn(CLAIMS[-1],result["inadmissible_claim_test_sources"])
        self.assertFalse(result["all_original_roles_and_claim_sources_complete"])

    def test_claim_wrong_source_and_omitted_support_are_rejected(self):
        over,cases,claims=fixture()
        over["positive_test_receipts"][-1]["test_path"] = (
            "verification/research/unregistered_claim.py")
        report=gate.route_coverage(over,cases,claims)
        self.assertIn(CLAIMS[-1],report["missing_claim_positive"])
        self.assertFalse(report["all_original_roles_and_claim_sources_complete"])
        over,cases,claims=fixture()
        over["compiler_axiom_receipts"][45]["declaration"]="Claim.False"
        report=gate.route_coverage(over,cases,claims)
        self.assertFalse(report["all_original_roles_and_claim_sources_complete"])
        self.assertTrue(report["missing_required_declaration_or_source"])

    def test_duplicate_evidence_id_and_forged_method_registry_rejected(self):
        over,cases,claims=fixture()
        over["positive_test_receipts"][1]["id"] = (
            over["positive_test_receipts"][0]["id"])
        with self.assertRaises(gate.EvidenceError):
            gate.route_coverage(over,cases,claims)
        over,cases,claims=fixture()
        case=cases["cases"][0]
        case["test_method_candidates"].append({
            "path":case["test_method_candidates"][0]["path"],
            "method":case["test_method_candidates"][0]["method"],
            "role":"SEMANTIC_NEGATIVE",
        })
        with self.assertRaises(gate.EvidenceError):
            gate.route_coverage(over,cases,claims)
