"""Python-only tests for the 25-case detached shard dispatcher.

Mocks exercise allocation and fail-closed metadata handling only; they are
never counted as successful Lean, real CI execution, or mathematical review.
"""
from pathlib import Path
import copy
import tempfile
import unittest
from unittest import mock
import json

import final_closure_all_original_semantics as all_cases
from final_closure_mutation_evidence import MutationEvidenceError

H = "a" * 40
T = "b" * 40


class SemanticShardingTests(unittest.TestCase):
    def test_exact_25_cases_once_across_nine_shards(self):
        shards = [all_cases.select_cases(i, 9) for i in range(9)]
        flat = [c for shard in shards for c in shard]
        self.assertEqual(len(flat), 25)
        self.assertEqual(set(flat), all_cases.EXPECTED)
        self.assertEqual(len(flat), len(set(flat)))
        self.assertTrue(all(len(x) in (2, 3) for x in shards))

    def test_invalid_shards_and_modified_inventory_fail_closed(self):
        for i, n in ((-1, 9), (9, 9), (0, 0), (0, 26)):
            with self.subTest(index=i, total=n):
                with self.assertRaises(MutationEvidenceError):
                    all_cases.select_cases(i, n)
        changed = dict(all_cases.batch.SPECS)
        changed.pop("A-05")
        with mock.patch.dict(all_cases.batch.SPECS, changed, clear=True):
            with self.assertRaises(MutationEvidenceError):
                all_cases.select_cases(0, 9)

    def test_fake_execution_cannot_self_assign_review_or_check_run(self):
        with tempfile.TemporaryDirectory(prefix="perm-original-shard-") as root:
            out = Path(root) / "detached"
            selected = all_cases.select_cases(0, 25)
            self.assertEqual(len(selected), 1)
            def fake_run(_head, cid, directory):
                self.assertEqual(cid, selected[0])
                directory.mkdir(parents=True, exist_ok=False)
                spec = all_cases.batch.SPECS[cid]
                return {
                    "format": "Permansson.OriginalSemanticMutantCandidate.v1",
                    "status": "DETACHED_UNREVIEWED_UNATTRIBUTED",
                    "source_head": H, "case_id": cid,
                    "test_path": spec["test_path"], "test_name": spec["method"],
                    "source_path": spec["source"],
                    "mutant_sha256": "c" * 64,
                    "detached_bundle_sha256": "d" * 64,
                    "mutation_record": {
                        "head_sha": H, "case_ids": [cid], "claim_ids": [],
                        "test_path": spec["test_path"],
                        "test_name": spec["method"],
                        "original_lean_source_path": spec["source"],
                        "mutant_source_sha256": "c" * 64,
                        "outcome": "REJECTED_SEMANTIC",
                        "compiler_exit_code": 1,
                        "check_run_id": None, "review_status": "NOT_RECEIVED",
                        "positive_control": {
                            "compiled": True, "exit_code": 0,
                            "lean_toolchain": "leanprover/lean4:v4.34.0",
                        },
                        "original_lean_source_sha256": "e" * 64,
                        "source_sha256": "f" * 64,
                    },
                    "ci_check_run_id": None, "independent_review": False,
                    "full_mathematical_acceptance": False,
                }
            with (
                mock.patch.object(all_cases, "git_head", return_value=H),
                mock.patch.object(all_cases.subprocess, "check_output",
                                  return_value=T),
                mock.patch.object(all_cases.batch, "run_one",
                                  side_effect=fake_run),
            ):
                out_record = all_cases.run_exact_shard(H, 0, 25, out)
            manifest = json.loads(
                (out / "unreviewed_shard_manifest.json").read_text())
            self.assertEqual(out_record["cases"], list(selected))
            self.assertEqual(manifest["case_ids"], list(selected))
            self.assertFalse(manifest["independent_review"])
            self.assertFalse(manifest["release_approved"])
            self.assertFalse(manifest["mathematical_acceptance"])
            self.assertIsNone(manifest["ci_check_run_id"])
            self.assertIn("UNREVIEWED", manifest["status"])
            with self.assertRaises(MutationEvidenceError):
                all_cases.run_exact_shard("bad", 0, 25, out)
    def test_attested_semantic_shard_rejects_fake_positive_or_approval(self):
        cid = all_cases.select_cases(0, 25)[0]
        spec = all_cases.batch.SPECS[cid]
        base = {
            "format": "Permansson.OriginalSemanticMutantCandidate.v1",
            "status": "DETACHED_UNREVIEWED_UNATTRIBUTED",
            "source_head": H, "case_id": cid,
            "test_path": spec["test_path"], "test_name": spec["method"],
            "source_path": spec["source"],
            "mutant_sha256": "c" * 64,
            "detached_bundle_sha256": "d" * 64,
            "mutation_record": {
                "head_sha": H, "case_ids": [cid], "claim_ids": [],
                "test_path": spec["test_path"],
                "test_name": spec["method"],
                "original_lean_source_path": spec["source"],
                "mutant_source_sha256": "c" * 64,
                "outcome": "REJECTED_SEMANTIC",
                "compiler_exit_code": 1,
                "check_run_id": None, "review_status": "NOT_RECEIVED",
                "positive_control": {
                    "compiled": True, "exit_code": 0,
                    "lean_toolchain": "leanprover/lean4:v4.34.0",
                },
                "original_lean_source_sha256": "e" * 64,
                "source_sha256": "f" * 64,
            },
            "ci_check_run_id": None, "independent_review": False,
            "full_mathematical_acceptance": False,
        }
        all_cases.validate_candidate_case(H, cid, base)
        changes = (
            lambda x: x.update(case_id="foreign"),
            lambda x: x.update(independent_review=True),
            lambda x: x.update(ci_check_run_id=999),
            lambda x: x["mutation_record"].update(head_sha="0" * 40),
            lambda x: x["mutation_record"].update(outcome="UNVERIFIED"),
            lambda x: x["mutation_record"].update(compiler_exit_code=0),
            lambda x: x["mutation_record"]["positive_control"].update(
                compiled=False),
            lambda x: x["mutation_record"].update(check_run_id=999),
            lambda x: x["mutation_record"].update(source_sha256="not-a-sha"),
            lambda x: x["mutation_record"].update(
                mutant_source_sha256="0" * 64),
        )
        for mutate in changes:
            row = copy.deepcopy(base)
            mutate(row)
            with self.subTest(mutate=mutate), self.assertRaises(
                    MutationEvidenceError):
                all_cases.validate_candidate_case(H, cid, row)



if __name__ == "__main__":
    unittest.main()
