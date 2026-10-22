"""Actual asymmetric common-update and world-input player-swap falsifier."""
from __future__ import annotations
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "PermanssonResearch/MultiAgent/AsymmetricCommonSwapFixture.lean"
OLD = "      generator.common liveUpdateInput {true} = 0 := by"
FALSE = "      generator.common liveUpdateInput {true} = 1 := by"
INVALID = re.compile(r"unknown (?:module|constant|identifier|tactic)|file not found|"
                     r"failed to import|unexpected token|parse error|out of memory|"
                     r"maximum heartbeat|object file|failed to synthesize", re.I)
SEMANTIC = re.compile(r"unsolved goals|Tactic .?simp.? failed|tactic .?simp.? made no progress|"
                      r"Tactic .?decide.? failed", re.I)


class AsymmetricPlayerSwap(unittest.TestCase):
    def test_source_bound_non_dirac_asymmetric_whole_path(self):
        module = "PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture"
        declarations = (
            "mixed_starts_distinct",
            "mixed_initial_positive_each_state",
            "mixed_initial_not_point_mass",
            "asymmetric_mixed_original_path_law_transport",
        )
        code = "import " + module + "\n" + "".join(
            "#check " + module + "." + item + "\n" +
            "#print axioms " + module + "." + item + "\n"
            for item in declarations
        )
        with tempfile.TemporaryDirectory(prefix="F01_mixed_", dir=ROOT / ".lake") as tmp:
            source = Path(tmp) / "F01Mixed.lean"
            source.write_text(code, encoding="utf-8")
            run = subprocess.run(
                ["lake", "env", "lean", str(source)], cwd=ROOT,
                capture_output=True, text=True, timeout=180,
            )
        output = run.stdout + run.stderr
        self.assertEqual(run.returncode, 0, output[-3500:])
        self.assertNotIn("sorryAx", output)
        self.assertNotIn("error:", output.lower())
        for item in declarations:
            self.assertIn(module + "." + item, output)

    def test_actual_common_update_false_same_input_claim(self):
        text = SOURCE.read_text(encoding="utf-8")
        self.assertEqual(text.count(OLD), 1)
        self.assertIn("asymmetric_original_path_law_transport", text)
        self.assertIsNotNone(shutil.which("lake"), "pinned Lean missing")
        positive = subprocess.run(
            ["lake", "env", "lean", str(SOURCE)], cwd=ROOT,
            capture_output=True, text=True, timeout=600,
        )
        self.assertEqual(positive.returncode, 0, positive.stdout + positive.stderr)
        changed = text.replace(OLD, FALSE)
        self.assertEqual(changed.count("import "), text.count("import "))
        with tempfile.TemporaryDirectory(prefix="F01_swap_", dir=ROOT / ".lake") as tmp:
            scratch = Path(tmp) / "FalseCommonUpdateValue.lean"
            scratch.write_text(changed, encoding="utf-8", newline="\n")
            result = subprocess.run(
                ["lake", "env", "lean", str(scratch)], cwd=ROOT,
                capture_output=True, text=True, timeout=600,
            )
        output = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, "unswapped common input silently accepted")
        self.assertIsNone(INVALID.search(output), output[-4000:])
        self.assertIsNotNone(SEMANTIC.search(output), output[-4000:])


if __name__ == "__main__":
    unittest.main()
