"""A source candidate is not a Lean proof or a reviewer approval."""
import json
import unittest
from unittest import mock

import pr113_implementation_matrix as m

H="a"*40
C=[f"C-{i:02}" for i in range(1,46)]
Q=["Q1","Q2","Q3","M1","M2","M3","N1","N2","N3","D8","D9"]


def fake_tree():
    proof="PermanssonResearch/Actual.lean"
    test="verification/research/test_actual.py"
    original={"format":"old","full45_accepted":False,"cases":[{
        "case_id":cid,"decision":"PENDING",
        "required_expected_result":"Original requirement "+cid
    } for cid in C]}
    cmap={"original_cases":45,"new_closure_owners":11,
          "cases":[{
          "case_id":cid,"required_expected_result":"Original requirement "+cid,
          "historical_contract_ids":["ORIGINAL"],
          "historical_proof_declarations":[{"name":"name","path":proof}],
          "test_method_candidates":[{"path":test,"method":"test_real",
                                     "role":"COMPILER_SOURCE"}],
          "remaining_obligations":["independent review"]
    } for cid in C]}
    claims={"count":11,"claims":[{
        "claim_id":cid,"accepted":False,
        "declarations":[{"declaration":"Module.theorem","path":proof}],
        "test_source_candidates":[test],"scope_exclusions":[]
    } for cid in Q]}
    inventory={"claims":[{"id":cid,"title":cid,"accepted":False} for cid in Q]}
    values={
        m.ORIGINAL:original,m.CASE_MAP:cmap,
        m.CLAIM_MAP:claims,m.INVENTORY:inventory,
    }
    contents={key:(json.dumps(val)+"\n").encode() for key,val in values.items()}
    contents[proof]=b"theorem name : True := by trivial\n"
    contents[test]=b"import unittest\nclass Test(unittest.TestCase):\n    def test_real(self):\n        self.assertTrue(True)\n"
    return contents


class MatrixTests(unittest.TestCase):
    def test_original_45_and_11_source_map_never_auto_certifies(self):
        files=fake_tree()
        result=m.produce(H,files.__getitem__)
        self.assertEqual(len(result["cases"]),45)
        self.assertEqual(len(result["claims"]),11)
        self.assertFalse(result["mathematical_certification"])
        self.assertEqual(result["unconditionally_implemented"],0)
        self.assertEqual(result["independently_accepted_cases"],0)
        self.assertEqual({r["implementation_state"] for r in result["cases"]},
                         {"PARTIAL"})
        self.assertEqual(result["cases"][0]["candidate_tests"][0]["source_status"],
                         "DISCOVERED_UNREVIEWED")

    def test_missing_theorem_or_test_is_not_source_complete(self):
        files=fake_tree()
        files.pop("PermanssonResearch/Actual.lean")
        r=m.produce(H,files.__getitem__)
        self.assertEqual(r["case_source_missing"],C)
        self.assertEqual(set(r["claim_source_missing"]),set(Q))
        files=fake_tree()
        files["verification/research/test_actual.py"]=b"def test_other(): pass\n"
        r=m.produce(H,files.__getitem__)
        self.assertEqual(len(r["case_source_missing"]),45)

    def test_original_requirement_mutation_blocks_matrix(self):
        files=fake_tree()
        raw=json.loads(files[m.CASE_MAP])
        raw["cases"][0]["required_expected_result"]="Changed premise"
        files[m.CASE_MAP]=json.dumps(raw).encode()
        with self.assertRaises(m.MatrixError):
            m.produce(H,files.__getitem__)

    def test_45_11_and_exact_claim_names_cannot_be_reduced(self):
        files=fake_tree()
        rows=json.loads(files[m.CASE_MAP])
        rows["cases"].pop()
        files[m.CASE_MAP]=json.dumps(rows).encode()
        with self.assertRaises(m.MatrixError):
            m.produce(H,files.__getitem__)
        files=fake_tree()
        rows=json.loads(files[m.CLAIM_MAP])
        rows["claims"][0]["claim_id"]="UNKNOWN"
        files[m.CLAIM_MAP]=json.dumps(rows).encode()
        with self.assertRaises(m.MatrixError):
            m.produce(H,files.__getitem__)

    def test_claim_historical_flag_cannot_be_relabelled(self):
        files=fake_tree()
        rows=json.loads(files[m.INVENTORY])
        rows["claims"][0]["accepted"]=True
        files[m.INVENTORY]=json.dumps(rows).encode()
        with self.assertRaises(m.MatrixError):
            m.produce(H,files.__getitem__)


if __name__=="__main__":
    unittest.main()
