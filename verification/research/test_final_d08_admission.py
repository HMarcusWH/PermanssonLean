"""D-08 restricted grammar: proof certificate must reject a forbidden typed block."""
import pathlib
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
PREFIX = (
    "import PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture\n"
    "open PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture\n"
    "open PermanssonResearch.GrammarRobust.BooleanDynamics\n"
    "open PermanssonResearch.GrammarRobust.AdversarialAdmission\n"
)


def lean(body):
    if not shutil.which("lake"):
        raise AssertionError("Lean compiler unavailable")
    with tempfile.TemporaryDirectory(dir=ROOT/".lake") as temp:
        f = pathlib.Path(temp)/"D08.lean"
        f.write_text(PREFIX + body + "\n")
        p = subprocess.run(("lake", "env", "lean", str(f)), cwd=ROOT,
                           capture_output=True, text=True, timeout=900)
    return p.returncode, p.stdout + p.stderr


class D08Admission(unittest.TestCase):
    def test_positive_signatures_and_axioms(self):
        names = ("forbidden_joint_not_in_restricted_menu",
                 "admitted_block_row_normalized", "restricted_joint_rejected")
        rc, output = lean("\n".join(
            "#check " + name + "\n#print axioms " + name for name in names))
        self.assertEqual(rc, 0, output)
        for name in names:
            self.assertIn(name, output)
        groups = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
        self.assertGreater(len(groups), 0, output)
        for item in groups:
            self.assertLessEqual(
                {x.strip() for x in item.split(",") if x.strip()},
                {"propext", "Classical.choice", "Quot.sound"})

    def test_false_frozen_joint_admission_is_semantic_mutant(self):
        rc, output = lean(
            "example : restricted.allowed joint := by\n"
            "  exact restricted_action_allowed\n")
        self.assertNotEqual(rc, 0, "forbidden joint was unexpectedly certified")
        self.assertNotRegex(output.lower(),
            r"unknown (module|identifier)|failed to import|parser error|out of memory|timed out")
        self.assertRegex(output.lower(), r"type mismatch|unsolved goals")


if __name__ == "__main__":
    unittest.main()
