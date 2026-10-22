"""B-02 actual original finite blockMargin proof and false generalization."""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MOD = "PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture"
DECLS = (
    "two_actual_minimal_original_blocks",
    "nonidentity_relabeling_preserves_actual_margin",
    "actual_local_minimality_transport_not_global_identity",
    "actual_coarsening_does_not_preserve_minimality",
    "and_joint_is_positive_but_not_minimal",
)


def compile_text(s):
    with tempfile.TemporaryDirectory(prefix="b02-original-", dir=ROOT / ".lake") as folder:
        p = Path(folder)/"Test.lean"
        p.write_text(s, encoding="utf-8")
        return subprocess.run(
            ["lake", "env", "lean", str(p)], cwd=ROOT,
            text=True, capture_output=True, timeout=300)


class B02OriginalMarginCompiler(unittest.TestCase):
    def test_actual_original_margin_minimality_and_axioms(self):
        log = "import " + MOD + "\n"
        for theorem in DECLS:
            log += "#check " + MOD + "." + theorem + "\n"
            log += "#print axioms " + MOD + "." + theorem + "\n"
        p = compile_text(log)
        diagnostic = p.stdout + p.stderr
        self.assertEqual(p.returncode, 0, diagnostic[-2500:])
        for theorem in DECLS:
            self.assertIn(MOD + "." + theorem, diagnostic)
        self.assertNotIn("error:", diagnostic.lower())
        self.assertNotIn("sorryAx", diagnostic)

    def test_false_joint_minimality_is_rejected_semantically(self):
        p = compile_text(
            "import " + MOD + "\n"
            "open PermanssonResearch.GrammarRobust\n"
            "open PermanssonResearch.GrammarRobust.BooleanMinimalityCases\n"
            "open PermanssonResearch.GrammarRobust.BooleanModel\n"
            "example : IsMinimalAllowed fine andPos ({0,1} : Finset (Fin 2)) := by\n"
            "  exact and_action_minimal\n"
        )
        diagnostic = (p.stdout + p.stderr).lower()
        self.assertNotEqual(p.returncode, 0, diagnostic[-2500:])
        self.assertTrue("type mismatch" in diagnostic, diagnostic[-2500:])
        for invalid in ("unknown identifier", "unknown module",
                        "sorryax", "maximum number of heartbeats", "parser error"):
            self.assertNotIn(invalid, diagnostic)


if __name__ == "__main__":
    unittest.main()
