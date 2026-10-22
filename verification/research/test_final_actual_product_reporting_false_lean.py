"""Q-03 dependent chronological mass / Q-04 intervention-side error mutants.

Original typed Lean constructions are imported. Q-03 rejects an additive
independent-error shortcut for the actual conditional three-stage law.
Q-04 rejects omitting the nonzero treated reporting error of the original
finite-prefix constitutive-margin certificate.
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
    r"maximum number of heartbeats|object file|timed out|"
    r"failed to synthesize", re.I)
SEMANTIC = re.compile(
    r"type mismatch|application type mismatch|unsolved goals|"
    r"tactic .?norm_num.? failed|proved.*false", re.I)


def reject(module, body):
    if shutil.which("lake") is None:
        raise AssertionError("pinned Lean compiler required")
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake",
                                     prefix="Q03Q04-source-") as td:
        path = Path(td) / "Mutant.lean"
        path.write_text("import " + module + "\n" + body + "\n",
                        encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(path)],
                                cwd=ROOT, capture_output=True, text=True,
                                timeout=900)
    log = result.stdout + "\n" + result.stderr
    if result.returncode == 0:
        raise AssertionError("false original-source theorem was accepted")
    if "error:" not in log.lower() or INVALID.search(log) or not SEMANTIC.search(log):
        raise AssertionError("incorrect failure kind:\n" + log[-4500:])
    return log


class OriginalConditionalMassAndErrorNegatives(unittest.TestCase):
    def test_Q_03_false_independent_error_mass(self):
        out = reject(
            "PermanssonResearch.Probability.DependentThreeStageSaturation",
            "open PermanssonResearch.Probability.DependentThreeStage\n"
            "example : dependentLaw.atom (true, (true,true)) = (9/20 : ℝ) := by\n"
            "  rw [true_history_mass]\n"
            "  norm_num\n"
        )
        self.assertIn("error:", out.lower())

    def test_Q_04_false_zero_intervention_report_error(self):
        out = reject(
            "PermanssonResearch.ConstitutiveQuasi.LocalizedPrefixExamples",
            "open PermanssonResearch.ConstitutiveQuasi.LocalizedExamples\n"
            "example : dist (0 : ℝ) (1/10) ≤ 0 := by\n"
            "  exact cannot_omit_treatment_report_error\n"
        )
        self.assertIn("error:", out.lower())


if __name__ == "__main__":
    unittest.main()
