"""D-09 native classwise-versus-barycenter semantics, and exact Lean mutant."""
from fractions import Fraction as Q
import pathlib
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
NAMESPACE = "PermanssonResearch.ReverseSolver.NonlinearMultichainAggregationFixture"


def compile_lean(body):
    if not shutil.which("lake"):
        raise AssertionError("Lean is required; no soft skip")
    with tempfile.TemporaryDirectory(dir=ROOT/".lake") as work:
        file = pathlib.Path(work)/"D09.lean"
        file.write_text(
            "import PermanssonResearch.ReverseSolver.NonlinearMultichainAggregationFixture\n"
            "open " + NAMESPACE + "\n" + body + "\n")
        p = subprocess.run(("lake", "env", "lean", str(file)), cwd=ROOT,
                           capture_output=True, text=True, timeout=900)
    return p.returncode, p.stdout + p.stderr


class D09Classwise(unittest.TestCase):
    def test_exact_expected_score_not_score_of_expected_law(self):
        F = lambda p: Q(1) - abs(p-Q(2,3))
        mixture = (F(Q(0))+F(Q(1)))/2
        averaged = F(Q(1,2))
        self.assertEqual(mixture,Q(1,2))
        self.assertEqual(averaged,Q(5,6))
        self.assertNotEqual(mixture,averaged)

    def test_compiled_distinct_physical_classes_and_nonlinear_lemma(self):
        names = ("physically_distinct_classes_with_shared_descriptor",
                 "nonlinear_classwise_aggregation_not_barycenter",
                 "actual_two_absorbing_full_path_mixture",
                 "exact_two_absorbing_rational_scores",
                 "actual_equal_weight_original_scores",
                 "actual_multichain_classwise_differs_from_barycenter")
        rc, out = compile_lean("\n".join(
            "#check "+name+"\n#print axioms "+name for name in names))
        self.assertEqual(rc, 0, out)
        for name in names:
            self.assertIn(name, out)
        groups = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", out)
        self.assertTrue(groups, out)
        for g in groups:
            self.assertLessEqual(
                {a.strip() for a in g.split(",") if a.strip()},
                {"propext", "Classical.choice", "Quot.sound"}, out)

    def test_wrong_barycenter_literal_fails_for_mathematical_reason(self):
        rc, out = compile_lean(
            "example : (1/2 : ℚ) = 5/6 := by\n"
            "  exact nonlinear_classwise_aggregation_not_barycenter.1\n")
        self.assertNotEqual(rc, 0, "arithmetic counterexample was laundered")
        self.assertNotRegex(out.lower(),
            r"unknown (module|identifier)|failed to import|parser error|out of memory|timed out")
        self.assertRegex(out.lower(), r"type mismatch|unsolved goals")


if __name__ == "__main__":
    unittest.main()
