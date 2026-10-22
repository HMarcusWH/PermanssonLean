"""Compile genuine Q-05 source in pinned Lean; reject mathematical false mutants."""
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MOD = "PermanssonResearch.Quotient.Q05ActualOriginalMarginWitnessFixture"
DECLS = (
    "fine_world_fixed", "coarse_world_fixed",
    "admitted_fine_world_fixed", "admitted_coarse_world_fixed",
    "twoStartDomain_has_distinct_starts",
    "entire_original_comparison_domain",
    "compression_noninjective",
    "actual_two_start_effects", "exact_margin_gap",
    "both_sides_every_strategic_row",
    "discounted_defect_budget", "two_sided_original_margin_bound",
    "treatment_reaches_other_strategic_state",
    "commonMass_normalization",
    "commonSourceKernel_mass",
    "commonEta_retention",
    "commonSourceKernel_retention",
    "commonEta_discounted_budget",
    "commonSourceKernel_not_exact",
)


def compile_text(source):
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake",
                                     prefix="q05-source-") as td:
        name = Path(td) / "Q05.lean"
        name.write_text(source, encoding="utf-8")
        return subprocess.run(["lake", "env", "lean", str(name)],
                              cwd=ROOT, capture_output=True, text=True,
                              timeout=300)


class ActualQ05SourceCompiler(unittest.TestCase):
    def test_actual_typed_primitive_models_and_axioms(self):
        base = "import " + MOD + "\n"
        probes = "".join(
            f"#check {MOD}.{name}\n#print axioms {MOD}.{name}\n"
            for name in DECLS)
        run = compile_text(base + probes)
        output = run.stdout + run.stderr
        self.assertEqual(run.returncode, 0, output[-3000:])
        for name in DECLS:
            self.assertIn(MOD + "." + name, output)
        self.assertNotIn("sorryAx", output)
        self.assertNotIn("error:", output.lower())

    def test_wrong_original_effect_cannot_compile(self):
        source = (
            f"import {MOD}\n"
            f"open {MOD}\n"
            "example : fineOriginalEffect false = (1/5 : ℚ) := by\n"
            "  exact (actual_two_start_effects false).1\n"
        )
        run = compile_text(source)
        output = (run.stdout + run.stderr).lower()
        self.assertNotEqual(run.returncode, 0, output[-3000:])
        for invalid in ("unknown identifier", "unknown module", "object file",
                        "sorryax", "maximum number of heartbeats",
                        "failed to import", "unexpected token"):
            self.assertNotIn(invalid, output)
        self.assertTrue("type mismatch" in output or "application type mismatch" in output,
                        output[-2500:])


    def test_false_claim_common_kernel_is_markov_rejected(self):
        source = (
            f"import {MOD}\n"
            f"open {MOD}\n"
            "example : commonSourceKernel false (false,false) Set.univ = 1 := by\n"
            "  exact commonSourceKernel_not_exact false (false,false)\n"
        )
        run = compile_text(source)
        log = (run.stdout + run.stderr).lower()
        self.assertNotEqual(run.returncode, 0, log[-3000:])
        for invalid in ("unknown identifier", "unknown module", "failed to import",
                        "sorryax", "maximum number of heartbeats", "unexpected token"):
            self.assertNotIn(invalid, log)
        self.assertTrue("type mismatch" in log or "has type" in log, log[-2500:])


if __name__ == "__main__":
    unittest.main()
