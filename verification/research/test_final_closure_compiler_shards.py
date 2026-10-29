"""Adversarial all45/all11 compiler-shard merging; fixtures are UNREVIEWED.

The mock compiler output is never represented as a real Lean execution or
a real authenticated Github check. This suite validates source binding,
coverage, decomposition, and refusal of missing/duplicate/altered shards.
"""
from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import final_closure_complete_lean_evidence as exporter
import final_closure_merge_compiler_shards as merger
from closure_elaborated_type import (
    BEGIN, END, elaborated_type_sha256
)

H = "a" * 40
SHA = lambda b: hashlib.sha256(b).hexdigest()


class CompleteCompilerShardTests(unittest.TestCase):
    def setUp(self):
        td = tempfile.TemporaryDirectory(prefix="perm-shard-unit-")
        self.addCleanup(td.cleanup)
        self.root = Path(td.name)
        self.repo = self.root / "checkout"
        self.repo.mkdir()
        self.shards = self.root / "shards"
        self.shards.mkdir()
        self.output = self.root / "combined"
        self.source = self.repo / "PermanssonResearch" / "Proof.lean"
        self.source.parent.mkdir(parents=True)
        self.source.write_text(
            "namespace Test\n"
            + "\n".join(f"theorem owner_{i} : True := by trivial"
                        for i in range(13))
            + "\nend Test\n")
        self.owners = [
            {"path": "PermanssonResearch/Proof.lean",
             "declaration": f"Test.owner_{i}",
             "case_ids": [f"C-{i:02}"],
             "claim_ids": ["Q1"] if i == 0 else []}
            for i in range(13)
        ]
        self.source_hash = SHA(self.source.read_bytes())
        self.digest = exporter.inventory_digest(self.owners)
        patcher1 = mock.patch.object(merger, "ROOT", self.repo)
        patcher2 = mock.patch.object(merger, "git_head", return_value=H)
        patcher1.start(); patcher2.start()
        self.addCleanup(patcher1.stop)
        self.addCleanup(patcher2.stop)
        self.write_shards(4)

    def row(self, idx):
        declaration = self.owners[idx]["declaration"]
        log = (
            f"{BEGIN}\nNAME={declaration}\nKIND=theorem\n"
            f"UNIVERSES=[]\nTYPE=Expr.const \u0060True []\n{END}\n"
            f"{declaration} depends on axioms: []\n"
        ).encode()
        record = {
            "declaration": declaration,
            "declaration_kind": "theorem",
            "universe_params_repr": "[]",
            "type_expr_repr": "Expr.const \u0060True []",
        }
        candidate = {
            "id": f"all:{idx:04}", "inventory_index": idx,
            "head_sha": H, "path": self.owners[idx]["path"],
            "declaration": declaration,
            "case_ids": self.owners[idx]["case_ids"],
            "claim_ids": self.owners[idx]["claim_ids"],
            "source_sha256": self.source_hash,
            "elaborated_type_sha256": elaborated_type_sha256(record),
            "declaration_kind": "theorem",
            "universe_params_repr": "[]",
            "transitive_axioms": [],
            "compiler_result": "PASS",
            "compiler_check": "research",
            "axiom_log_member": f"axiom_logs/all_{idx:04}.log",
            "axiom_log_sha256": SHA(log),
            "check_run_id": None,
        }
        return candidate, log

    def write_shards(self, count):
        for folder in self.shards.iterdir():
            if folder.is_dir():
                import shutil
                shutil.rmtree(folder)
        for i in range(count):
            dest = self.shards / f"shard-{i:02}"
            (dest/"axiom_logs").mkdir(parents=True)
            candidates = []
            for j in exporter.shard_indices(len(self.owners), i, count):
                row, log = self.row(j)
                candidates.append(row)
                (dest / row["axiom_log_member"]).write_bytes(log)
            manifest = {
                "format": "Permansson.AllCaseCompilerCandidate.v1",
                "status": "COMPILER_ONLY_UNREVIEWED",
                "head_sha": H,
                "proof_count": len(candidates),
                "inventory_count": len(self.owners),
                "inventory_sha256": self.digest,
                "shard_index": i,
                "shard_count": count,
                "case_count": 45, "claim_count": 11,
                "compiler_axiom_receipts": candidates,
                "independent_review": False,
                "authentic_ci_job_bound": False,
                "merged_main_sha": None,
            }
            (dest/"complete_compiler_candidate.json").write_text(
                json.dumps(manifest))

    def run_merge(self):
        return merger.merge(self.shards, self.output, head=H,
                            inventory=self.owners)

    def test_shards_partition_all_original_proofs_without_overlap(self):
        expected = set(range(len(self.owners)))
        for count in (1, 2, 3, 4, 7, 13):
            parts = [set(exporter.shard_indices(len(self.owners), i, count))
                     for i in range(count)]
            self.assertEqual(set.union(*parts), expected)
            self.assertEqual(sum(len(p) for p in parts), len(expected))
        for idx, count in ((-1, 4), (4, 4), (0, 0), (0, 17), (0, 14)):
            with self.subTest(idx=idx, count=count), self.assertRaises(
                    exporter.CompleteCompilerError):
                exporter.shard_indices(len(self.owners), idx, count)

    def test_complete_mock_merge_keeps_unreviewed_zero_approval(self):
        outcome = self.run_merge()
        self.assertEqual(outcome["proof_count"], len(self.owners))
        self.assertEqual(outcome["merged_shards"], 4)
        self.assertIsNone(outcome["check_run_id"])
        self.assertFalse(outcome["independent_review"])
        self.assertFalse(outcome["authentic_ci_job_bound"])
        self.assertEqual(outcome["status"], "COMPILER_ONLY_UNREVIEWED")
        self.assertTrue((self.output/"axiom_logs/all_0012.log").is_file())

    def test_missing_shard_never_looks_like_a_complete_release(self):
        import shutil
        shutil.rmtree(self.shards/"shard-02")
        with self.assertRaises(merger.ShardMergeError):
            self.run_merge()

    def test_swapped_or_duplicate_owner_never_fills_a_gap(self):
        folder = self.shards/"shard-01"
        manifest = folder/"complete_compiler_candidate.json"
        obj = json.loads(manifest.read_text())
        obj["compiler_axiom_receipts"][0]["inventory_index"] = 0
        manifest.write_text(json.dumps(obj))
        with self.assertRaises(merger.ShardMergeError):
            self.run_merge()

    def test_one_modified_theorem_body_invalidates_compiler_log_source(self):
        self.source.write_text(self.source.read_text() + "\n-- changed source\n")
        with self.assertRaises(merger.ShardMergeError):
            self.run_merge()

    def test_fake_axiom_type_hash_or_log_is_rejected(self):
        folder = self.shards/"shard-00"
        manifest = folder/"complete_compiler_candidate.json"
        obj = json.loads(manifest.read_text())
        obj["compiler_axiom_receipts"][0]["elaborated_type_sha256"] = "0"*64
        manifest.write_text(json.dumps(obj))
        with self.assertRaises(merger.ShardMergeError):
            self.run_merge()
        self.write_shards(4)
        (folder/"axiom_logs/all_0000.log").write_text(
            "Test.owner_0 depends on axioms: []")
        with self.assertRaises(merger.ShardMergeError):
            self.run_merge()

    def test_unexpected_member_or_wrong_full_inventory_hash_rejected(self):
        (self.shards/"shard-02"/"unrelated.txt").write_text("injected")
        with self.assertRaises(merger.ShardMergeError):
            self.run_merge()
        (self.shards/"shard-02"/"unrelated.txt").unlink()
        objpath = self.shards/"shard-02"/"complete_compiler_candidate.json"
        obj = json.loads(objpath.read_text())
        obj["inventory_sha256"] = "0"*64
        objpath.write_text(json.dumps(obj))
        with self.assertRaises(merger.ShardMergeError):
            self.run_merge()


if __name__ == "__main__":
    unittest.main()
