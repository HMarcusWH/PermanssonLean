"""M-02 original generator update key and exact marked-law counterexample.

These are compiler/semantic checks, NOT an independently reviewed case receipt.
"""
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MOD = "PermanssonResearch.MultiAgent.MarkedStrategicPathCountermodel"
THEOREMS = (
    "same_physical_P_for_both_actual_protocols",
    "actual_opponent_private_update",
    "same_allowed_anchor_update_key",
    "unequal_actual_update_rows",
    "original_strict_anchor_premise_rejected",
    "actual_opponent_action_fair",
    "source_aligned_atom",
    "source_crossed_atom",
    "unmarked_key_laws_identical",
    "marked_diagonal_separates",
    "unmarked_not_strict_certificate",
)


def compile_source(text):
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake",
                                     prefix="m02-source-") as folder:
        source = Path(folder) / "Check.lean"
        source.write_text(text, encoding="utf-8")
        return subprocess.run(
            ["lake", "env", "lean", str(source)],
            cwd=ROOT, text=True, capture_output=True, timeout=180)


class MarkedOriginalSourceTests(unittest.TestCase):
    def test_original_typed_generator_source_and_axioms(self):
        source = ("import " + MOD + "\n" +
                  "".join("#check " + MOD + "." + d + "\n" +
                          "#print axioms " + MOD + "." + d + "\n"
                          for d in THEOREMS))
        run = compile_source(source)
        log = run.stdout + "\n" + run.stderr
        self.assertEqual(run.returncode, 0, log[-3500:])
        for name in THEOREMS:
            self.assertIn(MOD + "." + name, log)
        self.assertNotIn("sorryAx", log)
        self.assertNotIn("error:", log.lower())

    def test_invalid_strict_autonomy_promotion_fails_semantically(self):
        source = (
            "import " + MOD + "\n" +
            "open " + MOD + "\n" +
            "example : PermanssonResearch.MultiAgent.IsStrictlyNonReactive "
            "opponent := by\n"
            "  exact original_strict_anchor_premise_rejected\n"
        )
        run = compile_source(source)
        log = run.stdout + "\n" + run.stderr
        self.assertNotEqual(run.returncode, 0, log[-2500:])
        self.assertIn("error:", log.lower())
        for fragment in ("unknown identifier", "unknown module", "unexpected token",
                         "sorryax", "maximum number of heartbeats"):
            self.assertNotIn(fragment, log.lower())
        self.assertTrue("type mismatch" in log.lower() or
                        "has type" in log.lower(),
                        log[-2500:])


if __name__ == "__main__":
    unittest.main()
