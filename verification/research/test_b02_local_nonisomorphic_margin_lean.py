"""B-02 original uniformly constitutive margin under local lower coverage.

Proves this using the actual Boolean physical atom bank and the original
blockMargin/constitutive comparison law, with a noninjective component
coarsening and a predeclared admission grammar. Positive source and a
mathematically false singleton-admission mutation are separate.
"""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MOD = "PermanssonResearch.GrammarRobust.B02LocalOriginalMarginClosure"
DECL = (
    "actualCoarsening_not_global_injective",
    "actualCoarsening_lift_full",
    "original_admitted_lower_coverage",
    "coarse_original_OR_positive",
    "coarse_original_OR_minimal",
    "original_local_minimality_without_global_isomorphism",
    "false_extra_admission_rejected",
)
ALLOW = {"propext", "Classical.choice", "Quot.sound"}


def compile_source(source):
    if shutil.which("lake") is None:
        raise AssertionError("pinned Lean required")
    with tempfile.TemporaryDirectory(prefix="B02-real-", dir=ROOT/".lake") as td:
        path = Path(td)/"Check.lean"
        path.write_text(source, encoding="utf-8")
        return subprocess.run(["lake", "env", "lean", str(path)],
                              cwd=ROOT, text=True, capture_output=True,
                              timeout=900)


class B02LocalOriginalProofs(unittest.TestCase):
    def test_original_nonisomorphic_local_margin_compiles(self):
        s = "import " + MOD + "\n" + "".join(
            "#check " + MOD + "." + name + "\n#print axioms " +
            MOD + "." + name + "\n" for name in DECL
        )
        p = compile_source(s)
        log = p.stdout + "\n" + p.stderr
        self.assertEqual(p.returncode, 0, log[-3500:])
        self.assertNotIn("error:", log.lower())
        self.assertNotIn("sorryAx", log)
        for name in DECL:
            self.assertIn(MOD+"."+name, log)
        rows = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log)
        self.assertTrue(rows, log)
        for row in rows:
            self.assertLessEqual(
                {a.strip() for a in row.split(",") if a.strip()}, ALLOW)

    def test_inadmissible_original_singleton_false_claim_rejected(self):
        s = (
            "import " + MOD + "\n"
            "open " + MOD + "\n"
            "example : fullOrEmptyFine.allowed ({0} : Finset (Fin 2)) := by\n"
            "  exact false_extra_admission_rejected\n"
        )
        p = compile_source(s)
        log = (p.stdout + "\n" + p.stderr).lower()
        self.assertNotEqual(p.returncode, 0, "forbidden singleton admitted")
        self.assertIn("error:", log)
        for bad in ("unknown identifier", "unknown module", "failed to import",
                    "unexpected token", "maximum number of heartbeats",
                    "sorryax", "out of memory"):
            self.assertNotIn(bad, log)
        self.assertRegex(log, r"type mismatch|unsolved goals|application type mismatch")


if __name__ == "__main__":
    unittest.main()
