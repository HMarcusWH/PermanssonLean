"""Eleven original claim-control selections are not self-awarding proofs."""
import unittest

import final_closure_claim_controls_candidate as claim


def fixture():
    claims = {}
    selected = []
    for index, cid in enumerate(sorted(claim.CLAIMS)):
        original = f"PermanssonResearch/Claim_{index}.lean"
        test = f"verification/research/test_claim_{index}.py"
        claims[cid] = {
            "claim_id":cid,
            "declarations":[{"path":original,
                             "declaration":f"Claim_{index}.statement"}],
            "test_source_candidates":[test],
        }
        selected.append({
            "claim_id":cid, "proof_source_path":original,
            "positive_test_path":test,"negative_test_path":test,
            "positive_test_class":"Controls",
            "negative_test_class":"Controls",
            "positive_test_method":f"test_positive_{index}",
            "negative_test_method":f"test_negative_{index}",
        })
    return {"format":claim.SELECTION,"claims":selected},claims


class ClaimOnlySelectionTests(unittest.TestCase):
    def test_all_eleven_source_owned_claims_are_required(self):
        data,scope=fixture()
        result=claim.selection_map(data,scope)
        self.assertEqual(set(result),set(claim.CLAIMS))
        self.assertEqual(len(result),11)

    def test_missing_or_borrowed_claim_and_source_rejected(self):
        changes=[
            lambda r:r["claims"].pop(),
            lambda r:r["claims"][0].update(claim_id="FOREIGN"),
            lambda r:r["claims"][0].update(
                proof_source_path="PermanssonResearch/Unrelated.lean"),
            lambda r:r["claims"][0].update(
                positive_test_path="verification/research/test_wrong.py"),
            lambda r:r["claims"][0].update(
                negative_test_method=r["claims"][0]["positive_test_method"]),
            lambda r:r["claims"][0].update(approved=True),
        ]
        for i,mutation in enumerate(changes):
            with self.subTest(i=i):
                data,scope=fixture()
                mutation(data)
                with self.assertRaises(claim.ClaimControlError):
                    claim.selection_map(data,scope)

    def test_one_forged_claim_does_not_replace_all_other_claims(self):
        data,scope=fixture()
        data["claims"]=[data["claims"][0]]*11
        with self.assertRaises(claim.ClaimControlError):
            claim.selection_map(data,scope)
