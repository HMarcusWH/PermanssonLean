"""Compile real B-01 overlap and semantically falsify a compatible-row claim."""
from __future__ import annotations
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "PermanssonResearch/GrammarRobust/BooleanOverlapFixture.lean"
VALID = ("theorem genuinely_compatible :\n"
         "    selectedFalse.Compatible wideFalse := by")
FALSE = ("theorem genuinely_compatible :\n"
         "    selectedFalse.Compatible selectedTrue := by")
INVALID = re.compile(
    r"unknown (?:module|identifier|constant|tactic)|file not found|"
    r"failed to import|unexpected token|parser error|out of memory|"
    r"maximum heartbeat|timed out|object file|failed to synthesize",
    re.I,
)
SEMANTIC = re.compile(r"Tactic .?rfl.? failed|unsolved goals|type mismatch", re.I)


class RealCompatibleOverlap(unittest.TestCase):
    def test_positive_and_false_compatibility_compile(self):
        self.assertTrue(SOURCE.is_file())
        positive = SOURCE.read_text(encoding="utf-8")
        self.assertEqual(positive.count(VALID), 1)
        self.assertIn("theorem incompatible_order_changes_actual_kernel", positive)
        self.assertIsNotNone(shutil.which("lake"), "real pinned Lean required")
        baseline = subprocess.run(
            ["lake", "env", "lean", str(SOURCE)], cwd=ROOT,
            capture_output=True, text=True, timeout=600,
        )
        self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
        mutant = positive.replace(VALID, FALSE)
        self.assertNotEqual(mutant, positive)
        self.assertEqual(mutant.count("import "), positive.count("import "))
        with tempfile.TemporaryDirectory(prefix="overlap_B01_", dir=ROOT / ".lake") as tmp:
            candidate = Path(tmp) / "FalseButWellTypedCompatibility.lean"
            candidate.write_text(mutant, encoding="utf-8", newline="\n")
            failure = subprocess.run(
                ["lake", "env", "lean", str(candidate)], cwd=ROOT,
                capture_output=True, text=True, timeout=600,
            )
        output = failure.stdout + failure.stderr
        self.assertNotEqual(failure.returncode, 0, "false compatibility accepted")
        self.assertIsNone(INVALID.search(output), output[-5000:])
        self.assertIsNotNone(SEMANTIC.search(output), output[-5000:])


if __name__ == "__main__":
    unittest.main()
