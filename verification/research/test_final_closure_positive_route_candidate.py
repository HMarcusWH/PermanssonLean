"""Positive-method route selection is never interchangeable with negative."""
import copy
import unittest

import final_closure_positive_route_candidate as positive

CASEIDS=[f"C-{i:02d}" for i in range(1,46)]

def fixture():
    cases=[]
    rows=[]
    for n,cid in enumerate(CASEIDS):
        test_path=f"verification/research/test_case_{n}.py"
        neg_path=f"verification/research/test_false_{n}.py"
        method=f"test_positive_{n}"
        proof_path=f"PermanssonResearch/Case_{n}.lean"
        cases.append({
            "case_id":cid,
            "historical_proof_declarations":[
                {"path":proof_path,"name":f"Case_{n}.trueStatement"}],
            "test_method_candidates":[
                {"path":test_path,"method":method,"role":"EXACT_CHECK"},
                {"path":neg_path,"method":f"test_false_{n}",
                 "role":"SEMANTIC_NEGATIVE"}],
        })
        rows.append({"case_id":cid,"test_path":test_path,
                     "test_class":"ScopeTests","test_method":method,
                     "proof_source_path":proof_path})
    return {"format":positive.SELECTION,"cases":rows},{"cases":cases}

class OriginalPositiveRoutesTests(unittest.TestCase):
    def test_all_forty_five_correct_positive_roles(self):
        mapped,scope=fixture()
        result=positive.parse_selection(mapped,scope)
        self.assertEqual(set(result),set(CASEIDS))
        self.assertEqual(len(result),45)

    def test_cannot_promote_semantic_negative_to_positive_role(self):
        mapped,scope=fixture()
        mapped["cases"][0]["test_path"]=scope["cases"][0]["test_method_candidates"][1]["path"]
        mapped["cases"][0]["test_method"]=scope["cases"][0]["test_method_candidates"][1]["method"]
        with self.assertRaises(positive.PositiveRouteError):
            positive.parse_selection(mapped,scope)

    def test_missing_or_alien_selected_lean_owner_never_valid(self):
        changes=[
            lambda m,s:m["cases"].pop(),
            lambda m,s:m["cases"][0].update(
                proof_source_path="PermanssonResearch/Other.lean"),
            lambda m,s:m["cases"][0].update(case_id="MISSING-CASE"),
            lambda m,s:m["cases"][0].update(test_method="test_unregistered"),
            lambda m,s:m["cases"][0].update(test_class=""),
            lambda m,s:m["cases"][0].update(approved=True),
        ]
        for idx,change in enumerate(changes):
            with self.subTest(index=idx):
                mapped,scope=fixture()
                change(mapped,scope)
                with self.assertRaises(positive.PositiveRouteError):
                    positive.parse_selection(mapped,scope)
