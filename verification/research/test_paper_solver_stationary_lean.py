"""Required full-Research post-build solver signatures and kernel axiom audit.

The test invokes the actual pinned Lean audit. Missing/stale dependency records
are independently rebuilt; generated CI reports stay under .lake.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[2]


class SolverStationaryLeanIntegration(unittest.TestCase):
    def test_actual_solver_signatures_and_transitive_axioms(self):
        scratch = ROOT / ".lake/closure-build/solver-stationary-unittest"
        scratch.mkdir(parents=True, exist_ok=True)
        command = [sys.executable, "-B", str(ROOT /
            "verification/research/build_solver_stationary_receipt.py"),
            "--recheck-audit", "--output-dir", str(scratch.relative_to(ROOT))]
        env = dict(os.environ, LEAN_NUM_THREADS="2")
        run = subprocess.run(command, cwd=ROOT, env=env, capture_output=True,
                             text=True, encoding="utf-8", errors="replace", timeout=3600)
        log = scratch / "unittest.out"
        log.write_text(run.stdout+run.stderr, encoding="utf-8")
        self.assertEqual(run.returncode, 0, str(log)+"\n"+run.stdout[-2500:]+run.stderr[-2500:])
        receipt = json.loads((scratch / "solver_stationary_receipt.json").read_text(encoding="utf-8"))
        self.assertEqual(receipt["status"], "SCOPED_THEOREM_FORMALIZED")
        self.assertIsNone(receipt["source_H"])
        self.assertGreaterEqual(len(receipt["modules"]), 28)
        self.assertTrue(all(item["compiler"]["status"] == "PASS" and
                            item["compiler"]["returncode"] == 0 for item in receipt["modules"]))
        audit = receipt["signature_and_axiom_audit"]
        self.assertGreaterEqual(audit["declarations_audited"], 22)
        self.assertLessEqual(set(audit["axioms"]), {"propext", "Classical.choice", "Quot.sound"})
        output = (ROOT / audit["output"]).read_text(encoding="utf-8")
        for declaration in ("monitor_initialLaw_optimal_and_attained",
                            "rollingResidence_optimal_and_attained",
                            "referenceStationaryFamily_check", "referenceClassCandidate_eq_native",
                            "rectangular_game_law_saddle", "rationalObjective_eq_actual",
                            "stationary_menu_actual_optimal_and_attained",
                            "observedOccupationLimit_ae_correct"):
            self.assertIn(declaration, output)
        self.assertNotIn("sorryAx", output)


if __name__ == "__main__":
    unittest.main()
