"""Actual PR113 A2 successor Lean evidence, NOT original security approval.

Run the exact source-phase compiler, pinned Lean 4.34.0 library/axiom checks,
a positive control and four genuine failing semantic mutants. Historical A2
continues to execute separately under its unchanged historical contract.
"""
from __future__ import annotations
import json
from pathlib import Path
import tempfile
import unittest
from pr113_a2_compiler_route_v3 import select_compiler

ROOT = Path(__file__).resolve().parents[2]


class SuccessorA2CompilerExecution(unittest.TestCase):
    def test_real_current_source_positive_and_negative_lean(self):
        selected = select_compiler(ROOT)
        compiler = selected.module
        with tempfile.TemporaryDirectory(prefix="pr113-a2-") as tmp:
            folder = Path(tmp) / "evidence"
            record = compiler.verify(ROOT, folder, mode="focused")
            print("PR113_A2_SUCCESSOR_BEGIN")
            print(json.dumps(record, sort_keys=True))
            print("PR113_A2_SUCCESSOR_END")
            self.assertEqual(record["format"], selected.receipt_format)
            self.assertEqual(record["status"],
                             "SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING",
                             record.get("reason", "real successor compiler failed"))
            self.assertEqual(set(record["declarations"]), set(compiler.DECLS))
            self.assertEqual(set(record["mutations"]), set(compiler.MUTATIONS))
            self.assertTrue(record["source_unchanged"])
            self.assertFalse(record["historical_a2_verifier_replaced"])
            self.assertFalse(record["independent_security_review"])
            self.assertFalse(record["mathematical_acceptance"])
            labels = [x["label"] for x in record["commands"]]
            self.assertIn("positive_fixture", labels)
            self.assertIn("signatures_axioms", labels)
            for name in compiler.MUTATIONS:
                self.assertIn(name, labels)
            for entry in record["commands"]:
                log = folder / entry["log"]
                self.assertTrue(log.is_file(), entry["label"])
                print("PR113_A2_LOG_BEGIN", entry["label"])
                print(log.read_text(encoding="utf-8", errors="replace"))
                print("PR113_A2_LOG_END", entry["label"])
