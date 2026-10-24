"""Lean C11 evaluator source signatures and corrupted-stationarity adversary."""
import pathlib
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
HEAD = "import PermanssonResearch.ReverseSolver.NonlinearBooleanClassEvaluator\n" \
       "import PermanssonResearch.ReverseSolver.C11ReferenceExamples\n"


def compile_lean(body):
    if not shutil.which("lake"):
        raise AssertionError("pinned Lean is required; never skip")
    with tempfile.TemporaryDirectory(dir=ROOT/".lake") as folder:
        source = pathlib.Path(folder)/"C11Boolean.lean"
        source.write_text(HEAD + body + "\n")
        proc = subprocess.run(("lake", "env", "lean", str(source)), cwd=ROOT,
                              capture_output=True, text=True, timeout=900)
    return proc.returncode, proc.stdout + proc.stderr


class C11BooleanEvaluator(unittest.TestCase):
    def test_named_compiler_and_transitive_axioms(self):
        names = (
            "PermanssonResearch.ReverseSolver.NonlinearPeriodThree.booleanClassFunctional",
            "PermanssonResearch.ReverseSolver.NonlinearPeriodThree.boolean_rational_objective_eq_actual",
            "PermanssonResearch.ReverseSolver.NonlinearPeriodThree.certified_boolean_score_exact",
            "PermanssonResearch.ReverseSolver.C11.ReferenceExamples.corrupted_stationary_receipt_rejected",
        )
        rc, out = compile_lean("\n".join(
            "#check " + name + "\n#print axioms " + name for name in names))
        self.assertEqual(rc, 0, out)
        for name in names:
            self.assertIn(name, out)
        axioms = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", out)
        self.assertTrue(axioms, out)
        for a in axioms:
            self.assertLessEqual({x.strip() for x in a.split(",") if x.strip()},
                                 {"propext", "Classical.choice", "Quot.sound"}, out)

    def test_false_stationarity_accepted_mutant_rejected(self):
        rc, out = compile_lean(
            "open PermanssonResearch.ReverseSolver.C11\n"
            "open PermanssonResearch.ReverseSolver.C11.ReferenceExamples\n"
            "example : checkClassStationary periodic corruptedPeriodic = true := by\n"
            "  exact corrupted_stationary_receipt_rejected\n")
        self.assertNotEqual(rc, 0)
        self.assertNotRegex(out.lower(), r"unknown (module|identifier)|failed to import|parser error|out of memory|timed out")
        self.assertRegex(out.lower(), r"type mismatch|unsolved goals")


if __name__ == "__main__":
    unittest.main()
