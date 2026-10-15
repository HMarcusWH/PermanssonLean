"""Generated C11 input/receipt literal must compile with genuine Lean kernel."""
from __future__ import annotations
import copy
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
import unittest

from c11_stationary_execution import StationaryError, execute
from c11_emit_stationary_lean import emit_source

ROOT=Path(__file__).resolve().parents[2]

class C11LeanLiteralTests(unittest.TestCase):
    def setUp(self):
        self.example=execute({"n":2,"matrix":[["0","1"],["1","0"]],
                              "descriptor":[False,True]})

    def test_01_reject_forged_share(self):
        bad=copy.deepcopy(self.example)
        bad["classes"][0]["true_share"]="1"
        with self.assertRaises(StationaryError):emit_source(bad)

    def test_02_source_contains_complete_data(self):
        code=emit_source(self.example)
        for text in ["ClassStationaryCandidate 2","checkStationaryFamily",
                     "inducedKernel_isMarkov",
                     "member0_share","member0_native",
                     "member0_native_observed","completeFamily_accepted",
                     "#print axioms C11ReifiedFixture.member0_native_observed",
                     "#print axioms C11ReifiedFixture.completeFamily_accepted"]:
            self.assertIn(text,code)

    def compile_source(self, code):
        # The Lean proof checker is a release gate, not an optional extra.
        self.assertIsNotNone(shutil.which("lake"), "pinned Lean/Lake is required")
        with tempfile.TemporaryDirectory() as dirname:
            source = Path(dirname) / "C11ReifiedStationary.lean"
            source.write_text(code, encoding="utf-8")
            return subprocess.run(
                ["lake", "env", "lean", str(source)],
                cwd=ROOT, capture_output=True, text=True, timeout=600)

    def test_03_genuine_compiled_receipt(self):
        compiled = self.compile_source(emit_source(self.example))
        self.assertEqual(compiled.returncode, 0,
                         (compiled.stdout + compiled.stderr)[-5000:])
        # Audit every generated theorem whose conclusion is part of the
        # release claim, not only the arithmetic validation predicates.
        for name in ("member0_accepted", "member0_share", "member0_native",
                     "member0_native_observed", "completeFamily_accepted"):
            report = re.search(
                rf"'(?:C11ReifiedFixture\.)?{name}' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",
                compiled.stdout)
            self.assertIsNotNone(report, compiled.stdout[-3500:])
            axioms = {x.strip() for x in (report.group(2) or "").split(",")
                      if x.strip()}
            self.assertLessEqual(
                axioms, {"propext", "Classical.choice", "Quot.sound"})

    def test_04_kernel_rejects_tampered_emitted_stationary_weight(self):
        code = emit_source(self.example)
        start = code.index("def member0 : ClassStationaryCandidate 2 where")
        end = code.index("theorem member0_accepted", start)
        original = code[start:end]
        half = "((1 : ℚ) / (2 : ℚ))"
        self.assertEqual(original.count(half), 2)
        corrupted = original.replace(half, "(1 : ℚ)", 1)
        tampered = code[:start] + corrupted + code[end:]
        compiled = self.compile_source(tampered)
        self.assertNotEqual(compiled.returncode, 0,
                            "Lean accepted a changed stationary vector")
        self.assertIn("error:", compiled.stdout + compiled.stderr)

    def test_05_kernel_rejects_tampered_emitted_observed_share(self):
        code = emit_source(self.example)
        original = ("def member0_reportedTrue : ℚ :=\n"
                    "  ((1 : ℚ) / (2 : ℚ))")
        self.assertEqual(code.count(original), 1)
        tampered = code.replace(original,
                                "def member0_reportedTrue : ℚ :=\n  (1 : ℚ)")
        compiled = self.compile_source(tampered)
        self.assertNotEqual(compiled.returncode, 0,
                            "Lean accepted a changed claimed observed share")
        self.assertIn("error:", compiled.stdout + compiled.stderr)

if __name__=="__main__":
    unittest.main()
