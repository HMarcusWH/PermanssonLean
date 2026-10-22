"""D-02/D-03/D-05 original-source semantic false propositions in Lean.

These are NOT source-independent numerical tests. Each false proposition
uses the actual original residence monitor or the original two-stage
committed/rectangular probability laws. The imports, types and positive
controls are pinned; only mathematical contradiction can count.
"""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
INVALID = re.compile(
    r"unknown (?:module|identifier|constant|tactic)|failed to import|"
    r"unexpected token|parser error|out of memory|"
    r"maximum number of heartbeats|object file|timed out|"
    r"failed to synthesize", re.I
)
SEMANTIC = re.compile(
    r"type mismatch|application type mismatch|unsolved goals|"
    r"tactic .?decide.? proved that the proposition|"
    r"tactic .?norm_num.? failed", re.I
)


def lean(module, body):
    if shutil.which("lake") is None:
        raise AssertionError("pinned Lean compiler is required")
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake",
                                     prefix="D02D03D05-actual-") as td:
        p = Path(td) / "Negative.lean"
        p.write_text("import " + module + "\n" + body + "\n",
                     encoding="utf-8")
        return subprocess.run(["lake", "env", "lean", str(p)],
                              cwd=ROOT, capture_output=True, text=True,
                              timeout=900)


class OriginalChronologicalBoundaryNegatives(unittest.TestCase):
    def assert_genuine_false(self, module, code):
        result = lean(module, code)
        log = result.stdout + "\n" + result.stderr
        self.assertNotEqual(result.returncode, 0,
                            "a false original mathematical claim compiled")
        self.assertIn("error:", log.lower())
        self.assertIsNone(INVALID.search(log), log[-4500:])
        self.assertIsNotNone(SEMANTIC.search(log), log[-4500:])

    def test_D_02_false_retryable_residence_word(self):
        self.assert_genuine_false(
            "PermanssonResearch.ReverseSolver.CompactResidenceMonitor",
            "open PermanssonResearch.ReverseSolver.FiniteMonitor\n"
            "example :\n"
            "  (residenceScan (fun z : Bool => z = true) 1\n"
            "    [true, false, true, true]).2 = false := by\n"
            "  decide\n"
        )

    def test_D_03_false_danger_after_success_revokes_it(self):
        self.assert_genuine_false(
            "PermanssonResearch.ReverseSolver.AvoidResidenceMonitor",
            "open PermanssonResearch.ReverseSolver.FiniteMonitor\n"
            "example :\n"
            "  (avoidRun (fun b : Bool => b = true)\n"
            "    (fun b : Bool => b = false) 0 ((0,false),false)\n"
            "    [true, false]).1.2 = false := by\n"
            "  exact danger_after_success_does_not_undo\n"
        )

    def test_D_05_false_committed_rectangular_path_law_equality(self):
        self.assert_genuine_false(
            "PermanssonResearch.ReverseSolver.CommittedVsRectangularPathFixture",
            "open PermanssonResearch.ReverseSolver.CommittedVsRectangular\n"
            "example :\n"
            "  (pathLaw false true).expectation survivesBoth =\n"
            "    min ((pathLaw false false).expectation survivesBoth)\n"
            "        ((pathLaw true true).expectation survivesBoth) := by\n"
            "  rw [rectangular_actual_success,\n"
            "      committed_false_actual_success,\n"
            "      committed_true_actual_success]\n"
            "  have hneq : (1/100 : ℝ) ≠ 9/100 := by norm_num\n"
            "  exact hneq\n"
        )


if __name__ == "__main__":
    unittest.main()
