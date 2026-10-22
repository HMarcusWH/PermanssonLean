"""Compile genuine Q-05 original margin adapter, without filling domination holes.

A syntactically assembled theorem does not constitute full Q-05 source review.
The tester audits the complete elaborated conditional theorem and detects an
invalid attempt to turn the conditional bound into an unconditional proof.
"""
import subprocess
import tempfile
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
MOD = "PermanssonResearch.Quotient.Q05ActualOriginalMarginAdapter"
THEOREMS = (
    "sourcePointWitness",
    "finiteMeasureLeOfAtoms",
    "sourceDominationOfAtoms",
    "sourcePointWitnessOfAtoms",
    "fineJ_is_treated_source",
    "coarseJ_is_treated_source",
    "observedWorldScore_measurable",
    "observedWorldScore_bounded",
    "sourcePointWitness_budget",
    "original_margin_of_verified_source_domination",
)


def compile_source(s):
    with tempfile.TemporaryDirectory(prefix="q05-margin-", dir=ROOT / ".lake") as td:
        path = Path(td) / "Q05Adapter.lean"
        path.write_text(s, encoding="utf-8")
        return subprocess.run(["lake", "env", "lean", str(path)],
                              cwd=ROOT, capture_output=True, text=True,
                              timeout=300)


class Q05OriginalMarginAdapterCompiler(unittest.TestCase):
    def test_exact_original_margin_type_and_axiom_dependencies(self):
        text = "import " + MOD + "\n" + "".join(
            f"#check {MOD}.{name}\n#print axioms {MOD}.{name}\n"
            for name in THEOREMS)
        run = compile_source(text)
        output = run.stdout + run.stderr
        self.assertEqual(run.returncode, 0, output[-3500:])
        for name in THEOREMS:
            self.assertIn(MOD + "." + name, output)
        self.assertNotIn("error:", output.lower())
        self.assertNotIn("sorryAx", output)

    def test_unproved_source_domination_cannot_be_ignored(self):
        mutant = (
            "import " + MOD + "\n"
            "open " + MOD + "\n"
            "example : VerifiedSourceDomination := by\n"
            "  trivial\n"
        )
        result = compile_source(mutant)
        output = (result.stdout + result.stderr).lower()
        self.assertNotEqual(result.returncode, 0,
                            "actual all-state domination was silently assumed")
        self.assertIn("error:", output)
        for fragment in ("unknown identifier", "unknown module", "parser error",
                         "sorryax", "maximum number of heartbeats"):
            self.assertNotIn(fragment, output)
        self.assertTrue("unsolved goals" in output or
                        "no goals to be solved" in output or
                        "tactic" in output, output[-3000:])


if __name__ == "__main__":
    unittest.main()
