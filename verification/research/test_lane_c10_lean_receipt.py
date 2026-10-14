"""Exact C10 JSON-to-Lean literal integration.

This intentionally checks a separate generated file with the real Lean
compiler, rather than claiming Python JSON parsing is formally verified.
"""
import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from c10_golden import create_golden
from c10_emit_lean_receipt import emit_source
from c10_verify_receipt import ReceiptError


ROOT = Path(__file__).resolve().parents[2]


class C10LeanReceiptTests(unittest.TestCase):
    def test_receipt_reifier_rejects_tampered_value(self):
        with tempfile.TemporaryDirectory() as d:
            receipt = create_golden(d)
            receipt["members"][1]["margin"] = "2/3"
            with self.assertRaises(ReceiptError):
                emit_source(receipt)

    def test_emitted_golden_compiles_with_lean_kernel(self):
        if not shutil.which("lake"):
            self.skipTest("Lean toolchain unavailable locally; required in Research Lean CI")
        with tempfile.TemporaryDirectory() as d:
            receipt = create_golden(d)
            source = emit_source(receipt)
            target = Path(d) / "C10ReifiedGolden.lean"
            target.write_text(source, encoding="utf-8")
            p = subprocess.run(
                ["lake", "env", "lean", str(target)],
                cwd=ROOT, capture_output=True, text=True, timeout=600
            )
            self.assertEqual(p.returncode, 0, p.stdout + "\n" + p.stderr)
            self.assertIn("axioms", source)
            self.assertIn("reifiedReceipt_valid", source)
            self.assertNotIn("native_decide", source)


if __name__ == "__main__":
    unittest.main()
