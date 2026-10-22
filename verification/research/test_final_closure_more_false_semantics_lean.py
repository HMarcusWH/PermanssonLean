"""Further source-grounded semantic false claims: F-02/F-04/F-05/Q-02.

Mathematical falsehoods: a frozen nonstationary real clock cannot stall;
a genuinely correlated Bernoulli joint action cannot be a product measure;
two observationally identical SCMs need not have equal joint interventions;
and zero transition mismatch does not erase a nonzero initial-law budget.
The probes require real pinned Lean and reject invalid diagnostic shortcuts.
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
    r"unexpected token|parse error|parser error|out of memory|"
    r"maximum number of heartbeats|failed to synthesize|"
    r"object file|timed out", re.I)
SEMANTIC = re.compile(
    r"type mismatch|unsolved goals|tactic .?(?:simp|norm_num|exact).? failed|"
    r"application type mismatch|tactic .?decide.? proved", re.I)


def check_false_source(module, body):
    if shutil.which("lake") is None:
        raise AssertionError("pinned Lean required")
    with tempfile.TemporaryDirectory(prefix="strict-negative-", dir=ROOT/".lake") as td:
        path = Path(td)/"False.lean"
        path.write_text("import " + module + "\n" + body, encoding="utf-8")
        r = subprocess.run(["lake", "env", "lean", str(path)],
                           cwd=ROOT, text=True, capture_output=True, timeout=900)
    return r.returncode, r.stdout + "\n" + r.stderr


class MoreActualSourceNegatives(unittest.TestCase):
    def fail_mathematically(self, module, body):
        status, out = check_false_source(module, body)
        self.assertNotEqual(status, 0, "original false claim was accepted")
        self.assertIn("error:", out.lower())
        self.assertIsNone(INVALID.search(out), out[-4000:])
        self.assertIsNotNone(SEMANTIC.search(out), out[-4000:])

    def test_F_02_false_stalled_original_natural_clock(self):
        self.fail_mathematically(
            "PermanssonResearch.MultiAgent.MeasurableNatClockFixture",
            "open MeasureTheory Set\n"
            "open PermanssonResearch.MultiAgent.MeasurableNatPrivateClock\n"
            "open PermanssonResearch.MultiAgent.MeasurableNatPrivateClock.RealFixture\n"
            "example (y : OldState (S0 := ℝ) (S1 := ℝ) (S2 := ℝ) (X := ℝ)) :\n"
            "  (anchor schedule Nat.succ).update\n"
            "    ((lift (0 : ℕ) y,(0,0)),0) (Set.univ ×ˢ {(0 : ℕ)}) = 1 := by\n"
            "  exact stalled_clock_rejected 0 y\n"
        )

    def test_F_04_false_product_representation_of_correlated_law(self):
        self.fail_mathematically(
            "PermanssonResearch.MultiAgent.ProtocolWitnesses",
            "import PermanssonResearch.X1.TypedModels\n"
            "open MeasureTheory ProbabilityTheory\n"
            "open PermanssonResearch.MultiAgent\n"
            "open PermanssonResearch.MultiAgent.Witness\n"
            "open PermanssonResearch.X1\n"
            "example : correlatedLaw = (coin (1/2)).prod (coin (1/2)) := by\n"
            "  haveI : IsProbabilityMeasure (coin (1/2)) :=\n"
            "    coin_probability _ (by norm_num)\n"
            "  exact correlatedLaw_ne_prod (coin (1/2)) (coin (1/2))\n"
        )

    def test_F_05_false_identification_of_original_joint_do(self):
        self.fail_mathematically(
            "PermanssonResearch.MultiAgent.FiniteMediation",
            "open PermanssonResearch.MultiAgent.FiniteMediation\n"
            "example : (nonidentificationSCM false).response () true false =\n"
            "  (nonidentificationSCM true).response () true false := by\n"
            "  obtain ⟨hfalse,htrue⟩ := two_SCMs_different_joint_do\n"
            "  rw [hfalse,htrue]\n"
            "  norm_num\n"
        )

    def test_Q_02_false_zero_initial_error_under_zero_row_defect(self):
        self.fail_mathematically(
            "PermanssonResearch.Probability.DiscountedInitialBudget",
            "open PermanssonResearch.Probability\n"
            "example : (∑' n : ℕ, (1-(1/3 : ℝ))*(1/3 : ℝ)^n *\n"
            "  (1-(1-(1/5 : ℝ))*(1-(0 : ℝ))^n)) = 0 := by\n"
            "  rw [zero_row_defect_retains_initial_budget\n"
            "    (show 0 ≤ (1/3 : ℝ) by norm_num)\n"
            "    (show (1/3 : ℝ) < 1 by norm_num)]\n"
            "  norm_num\n"
        )


if __name__ == "__main__":
    unittest.main()
