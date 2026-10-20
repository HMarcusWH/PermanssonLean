"""NEXT-05.1 — real compiler, hypothesis/type checks, and semantic mutants.

The test fails closed if a theorem is absent, any imported Lean build fails,
transitive axioms escape the original trusted list, or a false theorem is
accepted. A parser/import/typeclass failure is not a valid semantic rejection.
"""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "PermanssonResearch/MultiAgent/MeasurableProductTwoKernel.lean"
MODULE = "PermanssonResearch.MultiAgent.MeasurableProductTwoKernel"
PROBE = (
    f"import {MODULE}\n"
    "open PermanssonLean\n"
    "open PermanssonResearch.MultiAgent.FiniteProduct\n"
    "open PermanssonResearch.MultiAgent.MeasurableProduct\n"
    "open PermanssonResearch.MultiAgent.MeasurableProduct.Two\n"
    "#check update_map_two\n"
    "#check action_kernel_map_two\n"
    "#check world_kernel_pullback_two\n"
    "#check update_kernel_map_two\n"
    "#check compression_two\n"
    "#print axioms update_map_two\n"
    "#print axioms update_kernel_map_two\n"
    "#print axioms action_kernel_map_two\n"
    "#print axioms compression_two_state\n"
    "example (G : Generator ℝ (fun _ : Fin 2 => ℝ) ℝ "
    "(fun _ : Fin 2 => Bool)) :\n"
    "  ((assemble G).update).map strategicMap =\n"
    "    (((binary G).toGenerator).update).comap forwardUpdate "
    "measurable_forwardUpdate :=\n"
    "  update_kernel_map_two G\n"
)
FORBIDDEN = re.compile(
    r"unknown (module|identifier|constant|tactic)|file not found|"
    r"failed to import|unexpected token|parser error|out of memory|"
    r"maximum heartbeat|timed out|object file|failed to synthesize", re.I
)
AXIOM_ALLOWLIST = {"Classical.choice", "Quot.sound", "propext"}


def run_lean(text, filename, directory):
    path = directory / filename
    path.write_text(text, encoding="utf8")
    p = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                       capture_output=True, text=True, timeout=600)
    return p.returncode, p.stdout + p.stderr


class MeasurableKernelCompiler(unittest.TestCase):
    def test_full_source_signatures_and_axioms(self):
        self.assertTrue(SOURCE.is_file())
        self.assertIsNotNone(shutil.which("lake"), "pinned Lean/Lake required")
        with tempfile.TemporaryDirectory(prefix="next05kernel_", dir=ROOT / ".lake") as tmp:
            d = Path(tmp)
            ret, stdout = run_lean(PROBE, "KernelProbe.lean", d)
            self.assertEqual(ret, 0, stdout)
            self.assertNotIn("sorryAx", stdout)
            for name in ("update_map_two", "update_kernel_map_two",
                         "compression_two", "action_kernel_map_two"):
                self.assertIn(name, stdout)
            axiom_sets = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", stdout)
            self.assertGreaterEqual(len(axiom_sets), 4, stdout)
            for names in axiom_sets:
                actual = {v.strip() for v in names.split(",") if v.strip()}
                self.assertLessEqual(actual, AXIOM_ALLOWLIST, stdout)

    def test_well_typed_false_private_reindex_is_rejected(self):
        self.assertIsNotNone(shutil.which("lake"), "pinned Lean/Lake required")
        mutant = (
            f"import {MODULE}\n"
            "open PermanssonResearch.MultiAgent\n"
            "open PermanssonResearch.MultiAgent.MeasurableProduct.Two\n"
            "example (s : GameState Bool Bool Bool) :\n"
            "  strategicMap (inverseStrategicMap s) =\n"
            "    (s.1, (s.2.2, s.2.1)) := by\n"
            "  exact strategicMap_inverse s\n"
        )
        with tempfile.TemporaryDirectory(prefix="next05false_", dir=ROOT / ".lake") as tmp:
            ret, output = run_lean(mutant, "FalsePrivateSwap.lean", Path(tmp))
            self.assertNotEqual(ret, 0, "false well-typed map theorem compiled")
            self.assertIsNone(FORBIDDEN.search(output), output)
            self.assertTrue(
                any(x in output.lower() for x in ("type mismatch", "unsolved goals",
                                                  "application type mismatch")),
                output
            )


if __name__ == "__main__":
    unittest.main()
