"""Exact C10 JSON-to-Lean literal integration.

This intentionally checks a separate generated file with the real Lean
compiler, rather than claiming Python JSON parsing is formally verified.
"""
import json
import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from c10_golden import create_golden
from c10_emit_lean_receipt import emit_source
from c10_emit_golden_bridge import emit_golden_bridge
from c10_verify_receipt import ReceiptError


ROOT = Path(__file__).resolve().parents[2]


class C10LeanReceiptTests(unittest.TestCase):
    def assert_allowed_kernel_axioms(self, output: str, theorems=(
            "reifiedReceipt_valid", "reifiedReceipt_conditions")):
        """Audit every named generated proof term, not the #print source text."""
        allow = {"propext", "Classical.choice", "Quot.sound"}
        for theorem in theorems:
            matches = re.findall(
                rf"'{theorem}' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",
                output,
            )
            self.assertEqual(len(matches), 1, f"missing/ambiguous axioms report for {theorem}: {output}")
            marker, names = matches[0]
            if marker == "does not depend on any axioms":
                continue
            found = {v.strip() for v in names.split(",") if v.strip()}
            self.assertTrue(found.issubset(allow), f"unpermitted axiom(s) in {theorem}: {sorted(found - allow)}")

    def test_axiom_report_parser_rejects_extra_axiom(self):
        text = (
            "'reifiedReceipt_valid' depends on axioms: [propext, sorryAx]\n"
            "'reifiedReceipt_conditions' does not depend on any axioms\n"
        )
        with self.assertRaises(AssertionError):
            self.assert_allowed_kernel_axioms(text)

    def test_receipt_reifier_rejects_tampered_value(self):
        with tempfile.TemporaryDirectory() as d:
            receipt = create_golden(d)
            receipt["members"][1]["margin"] = "2/3"
            with self.assertRaises(ReceiptError):
                emit_source(receipt)


    def test_golden_bridge_refuses_other_input(self):
        with tempfile.TemporaryDirectory() as d:
            receipt = create_golden(d)
            receipt["normalized_input"]["descriptor"][0] = True
            from c10_exact_execution import check_input, execute
            modified = execute(check_input(receipt["normalized_input"]))
            with self.assertRaises(ReceiptError):
                emit_golden_bridge(modified)

    def test_emitted_golden_compiles_with_lean_kernel(self):
        if not shutil.which("lake"):
            self.skipTest("Lean toolchain unavailable locally; required in Research Lean CI")
        with tempfile.TemporaryDirectory() as d:
            receipt = create_golden(d)
            source = emit_golden_bridge(receipt)
            target = Path(d) / "C10ReifiedGolden.lean"
            target.write_text(source, encoding="utf-8")
            p = subprocess.run(
                ["lake", "env", "lean", str(target)],
                cwd=ROOT, capture_output=True, text=True, timeout=600
            )
            self.assertEqual(p.returncode, 0, p.stdout + "\n" + p.stderr)
            self.assert_allowed_kernel_axioms(p.stdout, (
                "reifiedReceipt_valid", "reifiedReceipt_conditions",
                "reifiedGolden_data_contract", "reifiedGolden_numeric_margins",
                "reifiedGolden_original_margins",
                "reifiedGolden_selection", "reifiedGolden_original_global_max",
                "PermanssonResearch.ReverseSolver.C10.six_original_baseline_exactGR",
            ))
            self.assertIn("reifiedReceipt_valid", source)
            self.assertNotIn("native_decide", source)


if __name__ == "__main__":
    unittest.main()
