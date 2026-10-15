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

    def assert_clean_compilation(self, code, class_count):
        """Compile each proof and audit the axioms of every emitted theorem."""
        compiled = self.compile_source(code)
        output = compiled.stdout + compiled.stderr
        self.assertEqual(compiled.returncode, 0, output[-6000:])
        names = ["completeFamily_accepted"]
        for i in range(class_count):
            names.extend((f"member{i}_accepted", f"member{i}_share",
                          f"member{i}_native", f"member{i}_native_observed"))
        for name in names:
            reports = re.findall(
                rf"'C11ReifiedFixture\.{re.escape(name)}' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",
                compiled.stdout)
            self.assertEqual(len(reports), 1,
                             f"expected one axiom report for {name}:\n{compiled.stdout[-4000:]}")
            axioms = {x.strip() for x in reports[0][1].split(",") if x.strip()}
            self.assertLessEqual(
                axioms, {"propext", "Classical.choice", "Quot.sound"}, name)
        self.assertNotIn("sorryAx", output)
        return compiled

    def assert_corruption_rejected_at(self, code, theorem_or_definition):
        """Verify an altered literal breaks its own proof obligation, not another stage."""
        compiled = self.compile_source(code)
        output = compiled.stdout + compiled.stderr
        self.assertNotEqual(compiled.returncode, 0,
                            "Lean accepted a modified source literal")
        lines = code.splitlines()
        marker = ("def " if theorem_or_definition == "kernel"
                  else "theorem ") + theorem_or_definition
        begin = next(i + 1 for i, line in enumerate(lines)
                     if line.startswith(marker))
        end = next((i + 1 for i, line in enumerate(lines[begin:], begin)
                    if line.startswith(("theorem ", "def ", "end "))),
                   len(lines) + 1)
        errors = [int(n) for n in re.findall(
            r"C11ReifiedStationary\.lean:(\d+):\d+: error:", output)]
        self.assertTrue(any(begin <= n < end for n in errors),
                        f"No proof rejection within {theorem_or_definition}:\n{output[-6000:]}")

    def test_03_genuine_compiled_receipt(self):
        self.assert_clean_compilation(emit_source(self.example), 1)

    def test_04_kernel_rejects_tampered_emitted_stationary_weight(self):
        code = emit_source(self.example)
        self.assert_clean_compilation(code, 1)
        start = code.index("def member0 : ClassStationaryCandidate 2 where")
        end = code.index("theorem member0_accepted", start)
        original = code[start:end]
        half = "((1 : ℚ) / (2 : ℚ))"
        self.assertEqual(original.count(half), 2)
        corrupted = original.replace(half, "(1 : ℚ)", 1)
        tampered = code[:start] + corrupted + code[end:]
        self.assert_corruption_rejected_at(tampered, "member0_accepted")

    def test_05_kernel_rejects_tampered_emitted_observed_share(self):
        code = emit_source(self.example)
        self.assert_clean_compilation(code, 1)
        original = ("def member0_reportedTrue : ℚ :=\n"
                    "  ((1 : ℚ) / (2 : ℚ))")
        self.assertEqual(code.count(original), 1)
        tampered = code.replace(original,
                                "def member0_reportedTrue : ℚ :=\n  (1 : ℚ)")
        self.assert_corruption_rejected_at(tampered, "member0_native_observed")


    def test_06_singleton_generated_fixture(self):
        report = execute({"n": 1, "matrix": [["1"]], "descriptor": [True]})
        self.assert_clean_compilation(emit_source(report), 1)

    def test_07_multiple_class_generated_fixture(self):
        report = execute({"n": 3, "matrix": [
            ["0", "1/3", "2/3"],
            ["0", "1", "0"],
            ["0", "0", "1"],
        ], "descriptor": [False, True, False]})
        self.assertEqual(len(report["classes"]), 2)
        self.assert_clean_compilation(emit_source(report), 2)

    def test_08_six_state_generated_fixture(self):
        from c10_golden import BASE
        report = execute({"n": 6, "matrix": BASE,
                          "descriptor": [False, False, True, True, True, True]})
        self.assertEqual(len(report["classes"]), 2)
        self.assert_clean_compilation(emit_source(report), 2)

    def test_09_kernel_rejects_tampered_emitted_transition_entry(self):
        code = emit_source(self.example)
        self.assert_clean_compilation(code, 1)
        start = code.index("def kernel :")
        end = code.index("def descriptor", start)
        original = code[start:end]
        cell = "(if y = (0 : Fin 2) then (0 : ℚ) else (1 : ℚ))"
        self.assertEqual(original.count(cell), 1)
        tampered = code[:start] + original.replace(
            cell, "(if y = (0 : Fin 2) then (0 : ℚ) else (0 : ℚ))", 1) + code[end:]
        self.assert_corruption_rejected_at(tampered, "kernel")

    def test_10_kernel_rejects_tampered_emitted_descriptor(self):
        code = emit_source(self.example)
        self.assert_clean_compilation(code, 1)
        original = "def descriptor : Fin 2 → Bool := fun x => (if x = (0 : Fin 2) then false else true)"
        self.assertEqual(code.count(original), 1)
        tampered = code.replace(original, original.replace("then false", "then true"), 1)
        self.assert_corruption_rejected_at(tampered, "member0_share")

if __name__=="__main__":
    unittest.main()
