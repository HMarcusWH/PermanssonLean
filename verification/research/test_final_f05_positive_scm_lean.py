"""F-05 positive-support original SCM instance and true-semantic Lean mutant."""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MODULE = "PermanssonResearch.MultiAgent.PositiveMediationWitness"
SOURCE = ROOT / "PermanssonResearch/MultiAgent/PositiveMediationWitness.lean"
PREFIX = ("import " + MODULE + "\n" +
          "open " + MODULE + "\n")
INVALID = re.compile(
    r"unknown (?:module|identifier|constant)|failed to import|parser error|"
    r"syntax error|maximum number of heartbeats|timed out|timeout|sorryAx",
    re.I)


def lean_probe(body):
    if not shutil.which("lake"):
        raise AssertionError("pinned Lean required; cannot skip formal F-05")
    with tempfile.TemporaryDirectory(dir=ROOT/".lake", prefix="f05-scm-") as temp:
        filename = Path(temp) / "Witness.lean"
        filename.write_text(PREFIX + body, encoding="utf-8")
        p = subprocess.run(["lake", "env", "lean", str(filename)], cwd=ROOT,
                           text=True, capture_output=True, timeout=600)
    return p.returncode, p.stdout + p.stderr


class PositiveOriginalSCMLean(unittest.TestCase):
    def test_compiled_positive_nonvacuous_identification_and_axioms(self):
        self.assertTrue(SOURCE.is_file())
        rc, output = lean_probe(
            "#check observationalMass_pos\n"
            "#check identified_for_every_treatment\n"
            "#check four_intervention_values\n"
            "#check mediator_shift_nonzero\n"
            "#print axioms identified_for_every_treatment\n"
            "#print axioms four_intervention_values\n"
            "example : exampleSCM.nestedExpectation true false = "
            "(10 / 3 : \u211d) := by\n"
            "  exact four_intervention_values.2.2.1\n")
        self.assertEqual(rc, 0, output[-4000:])
        self.assertNotRegex(output, INVALID)
        for name in ("observationalMass_pos", "identified_for_every_treatment",
                     "four_intervention_values", "mediator_shift_nonzero"):
            self.assertIn(name, output)
        reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
        self.assertTrue(reports, output)
        for values in reports:
            self.assertLessEqual(
                set(x.strip() for x in values.split(",") if x.strip()),
                {"propext", "Classical.choice", "Quot.sound"}, output)

    def test_wrong_positive_SCM_nested_equality_fails_semantically(self):
        rc, output = lean_probe(
            "example : exampleSCM.nestedExpectation true false = "
            "exampleSCM.nestedExpectation true true := by\n"
            "  rw [four_intervention_values.2.2.1,\n"
            "      four_intervention_values.2.2.2]\n"
            "  norm_num\n")
        self.assertNotEqual(rc, 0, "false SCM equality was accepted")
        self.assertNotRegex(output, INVALID)
        self.assertRegex(output.lower(),
                         r"unsolved goals|failed to prove|tactic .*failed|"
                         r"no goals to be solved")


if __name__ == "__main__":
    unittest.main()
