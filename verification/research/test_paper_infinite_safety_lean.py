"""The research lane exercises the actual infinite-safety signature/axiom audit."""
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]


class InfiniteSafetyLeanAudit(unittest.TestCase):
    def test_actual_infinite_safety_audit(self):
        output = ".lake/paper-closures-ci/infinite-safety"
        result = subprocess.run(
            [sys.executable, "-B", str(Path(__file__).with_name("build_infinite_safety_receipt.py")),
             "--recheck-audit", "--output-dir", output],
            cwd=ROOT, env=dict(os.environ, LEAN_NUM_THREADS="2"),
            capture_output=True, text=True, encoding="utf-8", timeout=1800,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        receipt = json.loads((ROOT / output / "infinite_safety_receipt.json").read_text(encoding="utf-8"))
        self.assertEqual(len(receipt["modules"]), 8)
        self.assertEqual(receipt["signature_and_axiom_audit"]["reports"], 15)
        self.assertIsNone(receipt["source_H"])
        self.assertTrue(all(r["compiler"]["status"] == "PASS" for r in receipt["modules"]))
        audit = receipt["signature_and_axiom_audit"]
        self.assertLessEqual(set(audit["observed_axioms"]), {"propext", "Classical.choice", "Quot.sound"})
        printed = (ROOT / audit["output"]).read_text(encoding="utf-8")
        for name in ("pathLaw_ae_chronological", "pathLaw_safeThrough", "limitValue_fixed_point",
                     "deterministic_stationary_infinite_optimum", "invariantCore_iff_almostSureSafety",
                     "invariantIterates_stable", "high_actual_finite_survival_zero_infinite"):
            self.assertIn(name, printed)
        self.assertNotIn("sorryAx", printed)


if __name__ == "__main__":
    unittest.main()
