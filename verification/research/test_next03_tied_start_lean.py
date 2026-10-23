"""X-04: same numeric equilibrium min cannot certify the full X1 B1 domain."""
from __future__ import annotations
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "PermanssonResearch/X1/TiedStartDomainFixture.lean"
ANCHOR = "end PermanssonResearch.X1.TiedStartDomain"
INVALID = re.compile(
    r"unknown (?:identifier|module|constant|tactic)|failed to import|"
    r"unexpected token|parse error|out of memory|heartbeat|"
    r"failed to synthesize|object file|no such file", re.I
)
FALSE_CLAIM = """theorem incorrectly_identical_B1 :
    omittedTiedStart = comparisonStarts := by
  exact omitted_domain_not_original

"""
SEMANTIC = re.compile(r"type mismatch|application type mismatch|unsolved goals", re.I)


class SameNumericMinNotSameDomain(unittest.TestCase):
    def test_lean_false_original_domain_mutation(self):
        source = SOURCE.read_text(encoding="utf-8")
        self.assertEqual(source.count(ANCHOR), 1)
        self.assertIn("omitted_domain_same_numeric_inf", source)
        self.assertIn("omitted_domain_not_original", source)
        self.assertIsNotNone(shutil.which("lake"), "pinned Lean compiler missing")
        positive = subprocess.run(["lake", "env", "lean", str(SOURCE)],
                                  cwd=ROOT, capture_output=True, text=True, timeout=600)
        self.assertEqual(positive.returncode, 0, positive.stdout + positive.stderr)
        altered = source.replace(ANCHOR, FALSE_CLAIM + ANCHOR)
        self.assertEqual(altered.count("import "), source.count("import "))
        self.assertEqual(altered.count("theorem incorrectly_identical_B1"), 1)
        with tempfile.TemporaryDirectory(prefix="X04_tie_", dir=ROOT / ".lake") as tmp:
            mutant = Path(tmp) / "FalseTiedDomain.lean"
            mutant.write_text(altered, encoding="utf-8", newline="\n")
            result = subprocess.run(["lake", "env", "lean", str(mutant)],
                                    cwd=ROOT, capture_output=True, text=True, timeout=600)
        output = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, "false full-domain equality compiled")
        self.assertIsNone(INVALID.search(output), output[-4000:])
        self.assertIsNotNone(SEMANTIC.search(output), output[-4000:])


if __name__ == "__main__":
    unittest.main()
