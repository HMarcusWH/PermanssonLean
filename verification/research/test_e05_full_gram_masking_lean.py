"""E-05 actual positive-gap Gram witness and false full-form negativity.

Imports the original signedGram_witness_value / witness-negative theorem and
a source-only additional positive summand. A false universal full-form sign
claim must be rejected for a mathematical type reason.
"""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MOD = "PermanssonResearch.Specialized.E05FullGramMaskingCountermodel"
DECLS = (
    "added_component_masks_actual_negative_gram",
    "original_signed_negative_but_total_positive",
    "extra_component_exceeds_negative_budget",
)
ALLOW = {"propext", "Classical.choice", "Quot.sound"}


def compile_lean(source):
    if shutil.which("lake") is None:
        raise AssertionError("pinned Lean compiler required")
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake",
                                     prefix="E05-gram-mask-") as td:
        path = Path(td) / "Probe.lean"
        path.write_text(source, encoding="utf-8")
        return subprocess.run(["lake", "env", "lean", str(path)],
                              cwd=ROOT, capture_output=True, text=True,
                              timeout=900)


class E05OriginalGramFullForm(unittest.TestCase):
    def test_original_signed_negative_and_masked_total_compiler(self):
        source = "import " + MOD + "\n"
        source += "".join(
            "#check " + MOD + "." + n + "\n#print axioms " +
            MOD + "." + n + "\n" for n in DECLS
        )
        run = compile_lean(source)
        output = run.stdout + "\n" + run.stderr
        self.assertEqual(run.returncode, 0, output[-4000:])
        for name in DECLS:
            self.assertIn(MOD + "." + name, output)
        self.assertNotIn("error:", output.lower())
        self.assertNotIn("sorryAx", output)
        groups = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
        self.assertTrue(groups, output)
        for group in groups:
            self.assertLessEqual(
                {x.strip() for x in group.split(",") if x.strip()},
                ALLOW, output
            )

    def test_false_unqualified_full_gram_negativity_rejected(self):
        source = (
            "import " + MOD + "\n"
            "open " + MOD + "\n"
            "open PermanssonResearch.Specialized\n"
            "open scoped InnerProductSpace\n"
            "example {E : Type*} [NormedAddCommGroup E]\n"
            "    [InnerProductSpace ℝ E] {c : ℝ} (hc : 0 < c)\n"
            "    (x y : E) (hgap : 0 < gramGap x y) :\n"
            "    c * (⟪x, gramWitness x y⟫_ℝ ^ 2 -\n"
            "         ⟪y, gramWitness x y⟫_ℝ ^ 2) +\n"
            "    2 * c * gramGap x y ^ 2 < 0 := by\n"
            "  exact (original_signed_negative_but_total_positive hc x y hgap).2\n"
        )
        run = compile_lean(source)
        output = (run.stdout + "\n" + run.stderr).lower()
        self.assertNotEqual(run.returncode, 0,
                            "source-disproved unqualified negativity accepted")
        for invalid in ("unknown module", "unknown identifier", "failed to import",
                        "parser error", "unexpected token", "out of memory",
                        "maximum number of heartbeats", "sorryax"):
            self.assertNotIn(invalid, output[-4000:])
        self.assertRegex(output, r"type mismatch|unsolved goals|application type mismatch")


if __name__ == "__main__":
    unittest.main()
