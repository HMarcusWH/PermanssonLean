"""M-02: original sampled-action/next-opponent-key marked source proofs.

Requires exact Lean elaboration, actual oneStepHistoryKernel.map opponentMark,
and a semantically rejected false diagonal assertion. A passing unmarked
state law alone is deliberately insufficient.
"""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MOD = "PermanssonResearch.MultiAgent.M02ActualMarkedHistoryFixture"
DECL = (
    "strictAnchor_isStrict",
    "markedLaw_actual_source_atom",
    "actual_unmarked_next_key_fair",
    "actual_unmarked_next_key_laws_equal",
    "actual_marked_diagonal_separation",
    "update_mechanisms_differ",
)
ALLOW = {"propext", "Classical.choice", "Quot.sound"}


def compile_lean(source):
    if shutil.which("lake") is None:
        raise AssertionError("pinned Lean required")
    with tempfile.TemporaryDirectory(prefix="M02-full-", dir=ROOT/".lake") as d:
        p = Path(d)/"Probe.lean"
        p.write_text(source, encoding="utf-8")
        return subprocess.run(["lake", "env", "lean", str(p)],
                              cwd=ROOT, capture_output=True,
                              text=True, timeout=900)


class M02RealMarkedHistory(unittest.TestCase):
    def test_real_marked_history_full_source_and_axioms(self):
        source = "import " + MOD + "\n"
        source += "".join("#check " + MOD + "." + d + "\n"
                          "#print axioms " + MOD + "." + d + "\n" for d in DECL)
        r = compile_lean(source)
        log = r.stdout + "\n" + r.stderr
        self.assertEqual(r.returncode, 0, log[-3800:])
        self.assertNotIn("error:", log.lower())
        self.assertNotIn("sorryAx", log)
        for d in DECL:
            self.assertIn(MOD+"."+d, log)
        rows = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log)
        self.assertTrue(rows, log)
        for row in rows:
            self.assertLessEqual(
                {v.strip() for v in row.split(",") if v.strip()}, ALLOW)

    def test_falsified_actual_marked_diagonal_is_rejected(self):
        source = (
            "import " + MOD + "\n"
            "open " + MOD + "\n"
            "example (y : PermanssonResearch.MultiAgent.MarkedStrategicPathCountermodel.Y) :\n"
            "  (∑ b : Bool, markedLaw true y {(b,((),b))}) = 1 := by\n"
            "  exact (actual_marked_diagonal_separation y).2\n"
        )
        r = compile_lean(source)
        log = (r.stdout+"\n"+r.stderr).lower()
        self.assertNotEqual(r.returncode, 0, "forged marked diagonal accepted")
        self.assertIn("error:", log)
        for invalid in ("unknown module", "unknown identifier",
                        "failed to import", "parser error",
                        "maximum number of heartbeats", "sorryax"):
            self.assertNotIn(invalid, log)
        self.assertRegex(log, r"type mismatch|unsolved goals|application type mismatch")


if __name__ == "__main__":
    unittest.main()
