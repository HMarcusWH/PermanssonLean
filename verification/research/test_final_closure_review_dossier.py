"""Pure adversarial candidate-dossier tests. No synthetic Lean/review acceptance."""
import unittest
from final_closure_review_dossier import make_dossier, ReviewDossierError

H = "a" * 40
T = "b" * 40
CLAIMS = ("Q1","Q2","Q3","M1","M2","M3","N1","N2","N3","D8","D9")


def fixture():
    ids = ["C-%02d" % i for i in range(1, 46)]
    proof = [{
        "id": "all:%04d" % i, "head_sha": H,
        "path": "PermanssonResearch/Proof%d.lean" % i,
        "declaration": "Demo.proof%d" % i,
        "case_ids": [ids[i % 45]], "claim_ids": [CLAIMS[i % 11]],
        "compiler_result": "PASS", "check_run_id": None,
        "transitive_axioms": ["propext"],
        "elaborated_type_sha256": "c"*64, "axiom_log_sha256": "d"*64,
    } for i in range(259)]
    originals = []
    candidates = {}
    for i, cid in enumerate(ids):
        theorem = proof[i]
        name = "test_false_%02d" % i
        originals.append({
            "case_id": cid, "required_expected_result": "synthetic criterion",
            "current_candidate_decision": "PENDING",
            "historical_proof_declarations": [
                {"path": theorem["path"], "name": theorem["declaration"]}],
            "test_method_candidates": [
                {"method": name, "role": "SEMANTIC_NEGATIVE",
                 "path": "verification/research/test_false.py"}],
        })
        candidates[cid] = {"route": "append" if i < 25 else "legacy",
                           "selected_semantic_methods": [name]}
    claims = [{
        "claim_id": claim,
        "declarations": [{"path": proof[i]["path"],
                          "declaration": proof[i]["declaration"]}],
    } for i, claim in enumerate(CLAIMS)]
    producers = [{
        "status": "CI_ARTIFACT_DIGEST_VERIFIED_UNREVIEWED",
        "head_sha": H, "artifact_id": 1000+i,
        "actual_check_run_id": 100+i,
        "independent_review": False, "mathematical_acceptance": False,
    } for i in range(21)]
    return dict(head=H, tree=T, original={"cases": originals},
                claim_map={"claims": claims},
                compiler={"compiler_axiom_receipts": proof},
                candidate_cases=candidates, producers=producers)


class ReviewDossierBoundaries(unittest.TestCase):
    def test_all_45_11_259_unreviewed(self):
        got = make_dossier(**fixture())
        self.assertEqual((got["case_count"], got["claim_count"],
                          got["compiler_target_count"]), (45, 11, 259))
        self.assertEqual((got["accepted_case_count"],
                          got["accepted_claim_count"]), (0, 0))
        self.assertTrue(all(x["accepted_case_decision"] is None
                            for x in got["case_dockets"]))
        self.assertFalse(got["release_approved"])

    def test_unchanged_original_theorem_is_mandatory(self):
        f = fixture()
        f["original"]["cases"][0]["historical_proof_declarations"][0][
            "name"] = "fake_original"
        with self.assertRaises(ReviewDossierError):
            make_dossier(**f)

    def test_missing_or_cross_case_false_method_blocks(self):
        f = fixture()
        f["candidate_cases"].pop("C-01")
        with self.assertRaises(ReviewDossierError):
            make_dossier(**f)
        f = fixture()
        f["candidate_cases"]["C-01"]["selected_semantic_methods"] = [
            "test_borrowed"]
        with self.assertRaises(ReviewDossierError):
            make_dossier(**f)

    def test_forged_producer_head_or_approval_blocks(self):
        f = fixture()
        f["producers"][0]["head_sha"] = "b"*40
        with self.assertRaises(ReviewDossierError):
            make_dossier(**f)
        f = fixture()
        f["producers"][0]["independent_review"] = True
        with self.assertRaises(ReviewDossierError):
            make_dossier(**f)

    def test_missing_compiler_claim_support_blocks(self):
        f = fixture()
        f["compiler"]["compiler_axiom_receipts"].pop()
        with self.assertRaises(ReviewDossierError):
            make_dossier(**f)
        f = fixture()
        f["claim_map"]["claims"].pop()
        with self.assertRaises(ReviewDossierError):
            make_dossier(**f)


if __name__ == "__main__":
    unittest.main()
