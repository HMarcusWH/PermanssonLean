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
        # A genuine common-source row has mass < 1. Treating it as
        # a defect-free probability kernel would erase the mandatory
        # discounted transport budget; the actual nonexactness theorem
        # refutes that false assertion, not an unfinished tactic.
        mutant = (
            "import " + MOD + "\n"
            "open " + MOD + "\n"
            "open PermanssonResearch.Quotient.Q05ActualOriginalMarginWitnessFixture\n"
            "example : (commonSourceKernel false) "
            "(false, false) Set.univ = 1 := by\n"
            "  exact commonSourceKernel_not_exact false (false, false)\n"
        )
        result = compile_source(mutant)
        output = (result.stdout + result.stderr).lower()
        self.assertNotEqual(result.returncode, 0,
                            "actual all-state domination was silently assumed")
        self.assertIn("error:", output)
        for fragment in ("unknown identifier", "unknown module", "parser error",
                         "sorryax", "maximum number of heartbeats"):
            self.assertNotIn(fragment, output)
        self.assertTrue("type mismatch" in output or
                        "application type mismatch" in output or
                        "unsolved goals" in output, output[-3000:])


if __name__ == "__main__":
    unittest.main()
