"""F-03 original typed infeasible strict opponent anchor.

The source constructs genuine nonempty pointwise legal sets and proves
the empty own-key fibre using the same original all-state semantics.
A false positive strict-anchor existential must be rejected by Lean,
not by a parser, missing import, or time/resource failure.
"""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MOD = "PermanssonResearch.MultiAgent.F03ActualInfeasibleAnchor"
DECLS = (
    "each_original_menu_nonempty",
    "both_starts_have_same_original_strict_key",
    "legal_fibre_empty_at_genuine_key",
    "no_feasible_original_strict_anchor",
    "all_pointwise_menus_nonempty_but_global_anchor_impossible",
)
ALLOW = {"propext", "Classical.choice", "Quot.sound"}


def compile_lean(source):
    if shutil.which("lake") is None:
        raise AssertionError("pinned Lean compiler required")
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake",
                                     prefix="F03-actual-") as td:
        file = Path(td) / "F03.lean"
        file.write_text(source, encoding="utf-8")
        return subprocess.run(["lake", "env", "lean", str(file)],
                              cwd=ROOT, capture_output=True, text=True,
                              timeout=600)


class OriginalStrictAnchorFibreTests(unittest.TestCase):
    def test_actual_all_state_legal_fibre_and_original_existence_theorems(self):
        source = "import " + MOD + "\n" + "".join(
            "#check " + MOD + "." + name + "\n#print axioms " +
            MOD + "." + name + "\n" for name in DECLS
        )
        result = compile_lean(source)
        out = result.stdout + "\n" + result.stderr
        self.assertEqual(result.returncode, 0, out[-4000:])
        self.assertNotIn("error:", out.lower())
        self.assertNotIn("sorryAx", out)
        for name in DECLS:
            self.assertIn(MOD + "." + name, out)
        found = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", out)
        self.assertTrue(found, out)
        for row in found:
            self.assertLessEqual({x.strip() for x in row.split(",") if x.strip()},
                                 ALLOW, out)

    def test_false_feasible_anchor_with_conflicting_own_fibre_rejected(self):
        source = (
            "import " + MOD + "\n"
            "open PermanssonResearch.MultiAgent\n"
            "open " + MOD + "\n"
            "example : ∃ a : PlayerTwoMechanism Unit Bool Unit Unit Unit Bool,\n"
            "  IsStrictlyNonReactive a ∧\n"
            "    ∀ y : Y, a.action y (legal y) = 1 := by\n"
            "  exact no_feasible_original_strict_anchor\n"
        )
        run = compile_lean(source)
        log = (run.stdout + "\n" + run.stderr).lower()
        self.assertNotEqual(run.returncode, 0, "mathematically false anchor accepted")
        for invalid in ("unknown module", "unknown identifier",
                        "failed to import", "unexpected token",
                        "maximum number of heartbeats", "out of memory"):
            self.assertNotIn(invalid, log[-4000:])
        self.assertRegex(log, r"type mismatch|unsolved goals|application type mismatch")


if __name__ == "__main__":
    unittest.main()
