"""Synthetic, non-certificate tests for real-producer-v2 preparation bridge."""
import copy
import unittest

from final_closure_producer_v2_bridge import (
    bind, verified_producer_index, ProducerBindingError
)
from final_closure_review_dossier import make_dossier
from test_final_closure_review_dossier import fixture

H = "a" * 40


def test_input():
    f = fixture()
    workflows = [
        ("compiler", ".github/workflows/pr113-all-case-compiler.yml",
         "pr113-compiler-shard-", 4),
        ("append", ".github/workflows/pr113-all-original-semantic-candidates.yml",
         "pr113-all-original-semantic-candidates-", 9),
        ("legacy", ".github/workflows/pr113-legacy-semantic-evidence.yml",
         "pr113-legacy-semantic-candidates-", 8),
    ]
    producers = []
    ident = 0
    for kind, workflow, prefix, count in workflows:
        for shard in range(count):
            ident += 1
            producers.append({
                "format": "Permansson.PR113.AuthenticatedProducerArtifact.v1",
                "status": "CI_ARTIFACT_DIGEST_VERIFIED_UNREVIEWED",
                "workflow_path": workflow,
                "artifact_name": prefix + str(shard),
                "run_id": 1200 + ["compiler","append","legacy"].index(kind),
                "run_attempt": 1,
                "job_id": 3000 + ident,
                "actual_check_run_id": 4000 + ident,
                "artifact_id": 5000 + ident,
                "artifact_sha256": "%064x" % ident,
                "manifest_sha256": "%064x" % (ident + 21),
                "head_sha": H,
                "independent_review": False,
                "mathematical_acceptance": False,
                "scientific_release_approved": False,
                "merged_main_sha": None,
            })
    lookup = verified_producer_index(H, producers)
    for i, (cid, cand) in enumerate(f["candidate_cases"].items()):
        kind = cand["route"]
        shard = i % 9 if kind == "append" else (i - 25) % 8
        p = lookup[(kind, shard)]
        cand["producing_artifact_id"] = p["artifact_id"]
        cand["actual_producing_check_run_id_provenance_only"] = (
            p["actual_check_run_id"])
        cand["accepted_semantic_negative"] = False
    full = f["compiler"]["compiler_axiom_receipts"]
    for i, proof in enumerate(full):
        proof.update({
            "inventory_index": i, "source_sha256": "f"*64,
            "compiler_check": "research", "axiom_log_member":
                f"axiom_logs/all_{i:04d}.log",
            "universe_params_repr": "[]",
        })
    dossier = make_dossier(**dict(f, producers=producers))
    manifest = {
        "head_sha": H,
        "status": "COMPILER_ONLY_UNREVIEWED",
        "proof_count": 259, "inventory_count": 259,
        "case_count": 45, "claim_count": 11,
        "authentic_ci_job_bound": False, "independent_review": False,
        "compiler_axiom_receipts": full,
    }
    return dossier, manifest, producers


class ExactProducerBoundBridge(unittest.TestCase):
    def test_all_259_45_11_have_correct_shard_provenance_never_accepted(self):
        d, compiler, producers = test_input()
        record = bind(H, d, compiler, producers)
        self.assertEqual(
            (record["proof_record_count"], record["case_record_count"],
             record["claim_record_count"]), (259, 45, 11))
        for proof in record["proof_producers"]:
            idx = proof["inventory_index"]
            self.assertEqual(proof["authenticated_producer"]["artifact_name"],
                             "pr113-compiler-shard-" + str(idx % 4))
            self.assertIsNone(proof["original_candidate_check_run_id"])
        self.assertFalse(record["strict_v2_ready"])
        self.assertFalse(record["mathematical_release_approved"])
        self.assertEqual(record["pending_explicit_review_scopes"], 56)
        self.assertEqual(record["accepted_cases"], 0)

    def test_duplicate_or_missing_producer_check_is_blocked(self):
        _, _, producers = test_input()
        broken = copy.deepcopy(producers)
        broken.pop()
        with self.assertRaises(ProducerBindingError):
            verified_producer_index(H, broken)
        broken = copy.deepcopy(producers)
        broken[2]["actual_check_run_id"] = broken[1]["actual_check_run_id"]
        with self.assertRaises(ProducerBindingError):
            verified_producer_index(H, broken)

    def test_stale_job_head_or_fake_approved_artifact_is_blocked(self):
        d, compiler, producers = test_input()
        other = copy.deepcopy(producers)
        other[0]["head_sha"] = "b"*40
        with self.assertRaises(ProducerBindingError):
            bind(H, d, compiler, other)
        other = copy.deepcopy(producers)
        other[0]["independent_review"] = True
        with self.assertRaises(ProducerBindingError):
            bind(H, d, compiler, other)

    def test_wrong_shard_and_borrowed_case_negative_are_blocked(self):
        d, compiler, producers = test_input()
        c = copy.deepcopy(compiler)
        c["compiler_axiom_receipts"][0]["inventory_index"] = 1
        with self.assertRaises(ProducerBindingError):
            bind(H, d, c, producers)
        d2 = copy.deepcopy(d)
        d2["case_dockets"][0]["producing_negative_candidate"][
            "actual_producing_check_run_id_provenance_only"] = 12345
        with self.assertRaises(ProducerBindingError):
            bind(H, d2, compiler, producers)

    def test_missing_original_claim_support_fails(self):
        d, compiler, producers = test_input()
        d2 = copy.deepcopy(d)
        d2["claim_dockets"][0]["compiler_receipt_ids"] = ["nonexistent"]
        with self.assertRaises(ProducerBindingError):
            bind(H, d2, compiler, producers)
        c = copy.deepcopy(compiler)
        c["compiler_axiom_receipts"].pop()
        with self.assertRaises(ProducerBindingError):
            bind(H, d, c, producers)


if __name__ == "__main__":
    unittest.main()
