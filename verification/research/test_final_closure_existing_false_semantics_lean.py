"""Original-source semantic rejection tests: X-06 and Appendix E.

These are actual false propositions of already-proved Lean non-implication
theorems. They must fail with theorem/type-goal diagnostics; import/parse/
resource failure is never accepted as mathematical evidence.

Separate independent reviewer approval remains mandatory for each case.
"""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
INVALID = re.compile(
    r"unknown (?:module|identifier|constant|tactic)|failed to import|"
    r"unexpected token|parser error|out of memory|"
    r"maximum number of heartbeats|object file|timeout|"
    r"failed to synthesize|invalid field notation", re.I)
SEMANTIC = re.compile(
    r"type mismatch|application type mismatch|unsolved goals|"
    r"tactic .?exact.? failed|type is not definitionally equal", re.I)


def challenge(module: str, body: str):
    if shutil.which("lake") is None:
        raise AssertionError("pinned Lean compiler required")
    with tempfile.TemporaryDirectory(prefix="original-semantic-",
                                     dir=ROOT / ".lake") as td:
        path = Path(td) / "FalseButWellTyped.lean"
        path.write_text("import " + module + "\n" + body + "\n",
                        encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(path)],
                                cwd=ROOT, capture_output=True, text=True,
                                timeout=900)
    out = result.stdout + "\n" + result.stderr
    return result.returncode, out


class OriginalNegativeSemanticBranches(unittest.TestCase):
    def assert_false_mathematical_result(self, module, body):
        rc, output = challenge(module, body)
        self.assertNotEqual(rc, 0, "mathematically forbidden result compiled")
        self.assertIn("error:", output.lower())
        self.assertIsNone(INVALID.search(output), output[-4000:])
        self.assertIsNotNone(SEMANTIC.search(output), output[-4000:])

    def test_X_06_false_exact_gr_under_real_leakage(self):
        self.assert_false_mathematical_result(
            "PermanssonResearch.X1.Comparison",
            "open MeasureTheory PermanssonResearch.X1\n"
            "example : PermanssonLean.RegimeSpecification.IsExactGeneratedRegime\n"
            "  (model Mode.equilibrium) (specification Mode.equilibrium)\n"
            "  (Measure.dirac y0) := by\n"
            "  exact replete_not_exactGR Mode.equilibrium\n"
            "    (specification Mode.equilibrium) rfl (Measure.dirac y0)\n"
        )

    def test_E_02_false_legal_negative_witness_from_illegal_approximation(self):
        self.assert_false_mathematical_result(
            "PermanssonResearch.Specialized.BoundaryWitnesses",
            "open PermanssonResearch.Specialized.BoundaryWitnesses\n"
            "example : ∃ p ∈ ({0} : Set ℝ), negativeForm p < 0 := by\n"
            "  exact exact_but_illegal_approximant.2.2.2\n"
        )

    def test_E_03_false_two_dimensional_shell_collapse(self):
        self.assert_false_mathematical_result(
            "PermanssonResearch.Specialized.BoundaryWitnesses",
            "open Matrix PermanssonResearch.Specialized\n"
            "open PermanssonResearch.Specialized.BoundaryWitnesses\n"
            "example :\n"
            "  let S := shellComplement (0 : Matrix (Fin 1) (Fin 1) ℝ)\n"
            "    (0 : Matrix (Fin 1) (Fin 2) ℝ) shell (-1)\n"
            "  S *ᵥ ![0, 1] = 0 := by\n"
            "  exact dimension_two_retains_second_equation.2.2.2\n"
        )

    def test_E_04_false_zero_shift_inverse(self):
        self.assert_false_mathematical_result(
            "PermanssonResearch.Specialized.BoundaryWitnesses",
            "open Matrix PermanssonResearch.Specialized\n"
            "open PermanssonResearch.Specialized.BoundaryWitnesses\n"
            "example : IsUnit\n"
            "  (negativeShift (0 : Matrix (Fin 1) (Fin 1) ℝ) 0) := by\n"
            "  exact zero_shift_does_not_supply_inverse\n"
        )


if __name__ == "__main__":
    unittest.main()
