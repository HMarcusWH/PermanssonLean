"""Q-05 unconditional typed source domination: actual kernel atoms, NOT only rates.

The successful case compiles every proof and checks transitive axioms. The
false case makes a deliberately wrong nonzero original atom claim, preserving
the exact math types and original source imports.
"""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MODULE = "PermanssonResearch.Quotient.Q05ActualAtomClosure"
DECLS = (
    "fine_induced_singleton",
    "coarse_induced_singleton",
    "common_source_singleton",
    "projected_common_singleton",
    "fine_actual_atom_domination",
    "coarse_actual_atom_domination",
    "original_verified_atom_domination",
    "original_point_witness",
    "actual_original_B1_margin_bound",
)
ALLOW = {"propext", "Classical.choice", "Quot.sound"}


def compiled(source):
    if shutil.which("lake") is None:
        raise AssertionError("pinned Lean compiler required")
    with tempfile.TemporaryDirectory(prefix="Q05-real-atom-", dir=ROOT/".lake") as d:
        file = Path(d) / "Probe.lean"
        file.write_text(source, encoding="utf-8")
        return subprocess.run(["lake", "env", "lean", str(file)],
                              cwd=ROOT, capture_output=True, text=True,
                              timeout=900)


class Q05UnconditionalSourceClosure(unittest.TestCase):
    def test_all_original_kernel_atoms_pointwitness_and_margin_compiler(self):
        content = "import " + MODULE + "\n" + "".join(
            "#check " + MODULE + "." + d + "\n#print axioms " +
            MODULE + "." + d + "\n" for d in DECLS
        )
        result = compiled(content)
        log = result.stdout + "\n" + result.stderr
        self.assertEqual(result.returncode, 0, log[-4500:])
        self.assertNotIn("error:", log.lower())
        self.assertNotIn("sorryAx", log)
        for d in DECLS:
            self.assertIn(MODULE + "." + d, log)
        lists = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log)
        self.assertTrue(lists, log)
        for item in lists:
            self.assertLessEqual(
                {a.strip() for a in item.split(",") if a.strip()}, ALLOW)

    def test_actual_baseline_nonzero_atom_cannot_be_erased(self):
        false_claim = (
            "import " + MODULE + "\n"
            "open " + MODULE + "\n"
            "open PermanssonResearch.Quotient.Q05ActualOriginalMarginWitnessFixture\n"
            "example : (fineModel false).inducedKernel (false,false)"
            " {(false,true)} = 0 := by\n"
            "  exact fine_induced_singleton false (false,false) (false,true)\n"
        )
        result = compiled(false_claim)
        log = (result.stdout + result.stderr).lower()
        self.assertNotEqual(result.returncode, 0, "wrong actual atom proved")
        for invalid in ("unknown identifier", "unknown module",
                        "failed to import", "unexpected token", "sorryax",
                        "maximum number of heartbeats", "out of memory"):
            self.assertNotIn(invalid, log[-4000:])
        self.assertRegex(log, r"type mismatch|unsolved goals|application type mismatch")


if __name__ == "__main__":
    unittest.main()
