"""N2 original native policy-class certification; no Unit/Fin6 model substitution.

All four Bool-only feedback maps remain deterministic stationary on the
physical observation, with identical native P/U. Compiler signatures,
axiom dependencies and semantic false-mutant behavior are checked directly.
"""
from fractions import Fraction
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
MODULE="PermanssonResearch.ReverseSolver.NonlinearPhaseBlindClassGeometry"
NAMES=(
    "native_false_preserving_true_mass_zero",
    "native_false_preserving_score",
    "native_true_after_false_score",
    "native_phase_blind_actual_le_five_sixths",
    "native_phase_blind_actual_attained",
    "native_actual_phase_aware_strictly_beats_phase_blind",
)


def lean_check(contents: str):
    if shutil.which("lake") is None:
        raise AssertionError("Pinned Lean toolchain required; no skipped mathematical tests")
    with tempfile.TemporaryDirectory(dir=ROOT/".lake") as dir:
        src=Path(dir)/"PhaseBlindOriginal.lean"
        src.write_text("import "+MODULE+"\n"
          "open PermanssonResearch.ReverseSolver.NonlinearPeriodThree\n"
          +contents+"\n")
        proc=subprocess.run(["lake","env","lean",str(src)],cwd=ROOT,
          capture_output=True,text=True,timeout=900)
    return proc.returncode,proc.stdout+proc.stderr


def score(true_probability: Fraction):
    return Fraction(1)-abs(true_probability-Fraction(2,3))


class NativePhaseBlindOriginalTests(unittest.TestCase):
    def test_exact_policy_scores_not_just_orbit_table(self):
        scores={(False,False):score(Fraction(0)),
                (False,True):score(Fraction(0)),
                (True,False):score(Fraction(1,2)),
                (True,True):score(Fraction(1))}
        self.assertEqual(scores[(True,False)],Fraction(5,6))
        self.assertEqual(max(scores.values()),Fraction(5,6))
        self.assertEqual(score(Fraction(2,3)),1)
        self.assertTrue(all(value<1 for value in scores.values()))

    def test_lean_original_canonical_expected_scores_and_axioms(self):
        rc,out=lean_check("\n".join(
           "#check "+name+"\n#print axioms "+name for name in NAMES))
        self.assertEqual(rc,0,out)
        for name in NAMES:
            self.assertIn(name,out)
        lists=re.findall(r"depends on axioms:\s*\[([^\]]*)\]",out)
        self.assertTrue(lists,"no transitive axiom records found: "+out)
        for row in lists:
            self.assertLessEqual({x.strip() for x in row.split(",") if x.strip()},
                                 {"propext","Classical.choice","Quot.sound"},out)
        self.assertNotIn("sorryAx",out)

    def test_false_unrestricted_optimum_is_rejected_mathematically(self):
        # Keep the false claim in the actual original score semantics, but
        # rewrite by the proved attainable value before the negative step.
        # A direct failed `exact` can exhaust whnf heartbeats while trying to
        # compare the unfolded infinite-path objective, which is NOT a
        # mathematical rejection. Here Lean reaches a literal false equality.
        rc,out=lean_check(
          "example : nativeExpectedNonlinearScore\n"
          "  (phaseBlindPolicy\n"
          "    PermanssonResearch.ReverseSolver.NonlinearOccupationBoundary.alternatingFeedback)\n"
          "    = (1 : ℝ) := by\n"
          "  rw [native_phase_blind_actual_attained]\n"
          "  have hneq : (5 / 6 : ℝ) ≠ 1 := by norm_num\n"
          "  exact hneq\n")
        self.assertNotEqual(rc,0,"false deterministic optimality was accepted")
        self.assertNotRegex(out.lower(),
          r"unknown (module|identifier)|failed to import|parser error|"
          r"out of memory|timed out|deterministic.*timeout|"
          r"maximum number of heartbeats|maximum recursion depth")
        self.assertRegex(out.lower(),r"type mismatch|unsolved goals|application type mismatch")

if __name__=="__main__":
    unittest.main()
