"""D-04 / D-06 original mathematical false-claim tests.

D-04 falsifies an illegal p=1 hard-risk choice using the real 17/20
finite budget result. D-06 falsifies equality of two actually reachable
posterior completion beliefs generated from ONE original prior with both
histories of positive probability.
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
    r"unexpected token|parse error|out of memory|"
    r"maximum number of heartbeats|object file|timed out|"
    r"failed to synthesize", re.I
)
SEMANTIC = re.compile(
    r"type mismatch|application type mismatch|unsolved goals|"
    r"tactic .?norm_num.? failed|proved.*false", re.I
)


def compile_lean(module, source):
    if shutil.which("lake") is None:
        raise AssertionError("pinned Lean toolchain required")
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake",
                                     prefix="D04D06-actual-") as td:
        path = Path(td)/"False.lean"
        path.write_text("import "+module+"\n"+source+"\n",
                        encoding="utf-8")
        return subprocess.run(["lake", "env", "lean", str(path)],
                              cwd=ROOT, text=True, capture_output=True,
                              timeout=900)


class OriginalRiskAndBeliefNegatives(unittest.TestCase):
    def reject_false(self, module, source):
        run = compile_lean(module, source)
        out = run.stdout + "\n" + run.stderr
        self.assertNotEqual(run.returncode, 0,
                            "mathematically false original-source conclusion accepted")
        self.assertIn("error:", out.lower())
        self.assertIsNone(INVALID.search(out), out[-3500:])
        self.assertIsNotNone(SEMANTIC.search(out), out[-3500:])

    def test_D_04_false_hard_risk_budget_accepts_p_one(self):
        self.reject_false(
            "PermanssonResearch.ReverseSolver.SolverBoundaryWitnesses",
            "open PermanssonResearch.ReverseSolver.SolverBoundaryWitnesses\n"
            "example : ((1 : ℚ) / 10 ≤ 1/20) := by\n"
            "  exact hard_risk_half_mixture_attains.2.2\n"
        )

    def test_D_06_false_same_readout_identifies_completion(self):
        self.reject_false(
            "PermanssonResearch.ReverseSolver.ReachableCompletionBeliefFixture",
            "open PermanssonResearch.ReverseSolver.ReachableCompletionBelief\n"
            "example : (model.filter 0 initial [(false, ())]).weight true =\n"
            "  (model.filter 0 initial [(true, ())]).weight true := by\n"
            "  rw [reachable_posteriors_disagree.1,\n"
            "      reachable_posteriors_disagree.2]\n"
            "  norm_num\n"
        )


if __name__ == "__main__":
    unittest.main()
