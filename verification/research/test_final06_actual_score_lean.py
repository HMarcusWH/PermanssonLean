"""Full explicit Lean kernel/canonical-path/conditional-score compiler signatures."""
import pathlib
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
MODULE = "PermanssonResearch.ReverseSolver.NonlinearPeriodThreeExpectedScore"
NAMES = (
    "native_inducedKernel_eq_deterministic",
    "native_pathLaw_dirac",
    "native_actual_occupation_ae_limit",
    "native_phase_orbit_is_cycle",
    "native_three_phase_true_share",
    "actual_phase_aware_score_one_of_canonical_true_mass",
    "native_phase_aware_actual_score_one",
    "actual_phase_blind_score_le_of_class_identification",
    "actual_restricted_gap_of_identified_classes",
)
ALLOW = {"propext", "Classical.choice", "Quot.sound"}


def run_lean(testcase, body):
    testcase.assertIsNotNone(shutil.which("lake"), "required compiler unavailable; no skip")
    with tempfile.TemporaryDirectory(dir=ROOT/".lake") as directory:
        path = pathlib.Path(directory)/"ActualScore.lean"
        path.write_text("import " + MODULE + "\n"
                        "open PermanssonResearch.ReverseSolver.NonlinearPeriodThree\n"
                        + body + "\n")
        result = subprocess.run(("lake", "env", "lean", str(path)), cwd=ROOT,
                                capture_output=True, text=True, timeout=900)
    return result.returncode, result.stdout + result.stderr


class NativeScoreCompiler(unittest.TestCase):
    def test_source_signatures_and_axioms(self):
        rc, out = run_lean(self, "\n".join(
            "#check " + name + "\n#print axioms " + name for name in NAMES))
        self.assertEqual(rc, 0, out)
        for name in NAMES:
            self.assertIn(name, out)
        sets = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", out)
        self.assertGreater(len(sets), 0, "no transitive axiom records: " + out)
        for item in sets:
            self.assertLessEqual(
                {x.strip() for x in item.split(",") if x.strip()}, ALLOW, out)
        self.assertNotIn("sorryAx", out)

    def test_false_native_cycle_score_rejected_semantically(self):
        rc, out = run_lean(self,
            "example : nativePeriodThreeShare = (1/2 : ℚ) := by\n"
            "  exact native_period_three_share\n")
        self.assertNotEqual(rc, 0, "incorrect true share accepted")
        self.assertNotRegex(out.lower(),
            r"unknown (module|identifier)|failed to import|parser error|out of memory|timed out")
        self.assertRegex(out.lower(), r"type mismatch|unsolved goals|application type mismatch")


if __name__ == "__main__":
    unittest.main()
