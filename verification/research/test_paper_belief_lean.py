"""Post-Research-build checks for finite hidden-state observation control.

The positive Lean fixture checks the strict hidden-information gap, zero
observation branches, successor readout timing, actual chronological history
marginals, and the necessity of retaining a hidden event flag. Every named
declaration in all six implementation modules is then audited transitively.
"""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import unittest


ROOT = Path(__file__).resolve().parents[2]


class BeliefLeanClosure(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = ROOT / ".lake/belief-paper-closure"
        scratch.mkdir(parents=True, exist_ok=True)
        cls.receipt_path = scratch / "fixture_receipt.json"
        fixture = ROOT / "verification/research/BeliefObservationWitness.lean"
        cls.receipt = {"status": "RUNNING", "fixture": {}, "source_sha256": {
            str(fixture.relative_to(ROOT)): hashlib.sha256(fixture.read_bytes()).hexdigest()}}
        pinned = os.environ.get("PERMANSSON_PAPER_LEAN") or os.environ.get("PERMANSSON_X1_LEAN")
        lean = [pinned] if pinned else ["lake", "env", "lean"]
        timeout = int(os.environ.get("PERMANSSON_PAPER_CHECK_TIMEOUT", "600"))
        started = time.monotonic()
        cls.receipt_path.write_text(json.dumps(cls.receipt, indent=2), encoding="utf-8")
        try:
            run = subprocess.run(lean + [str(fixture)], cwd=ROOT, capture_output=True,
                                 text=True, encoding="utf-8", timeout=timeout)
            output = run.stdout + run.stderr
            cls.receipt["fixture"] = {"status": "PASS" if run.returncode == 0 else "FAIL",
                                      "returncode": run.returncode,
                                      "elapsed": time.monotonic()-started}
        except (subprocess.TimeoutExpired, OSError) as exc:
            output = str(exc)
            cls.receipt["fixture"] = {"status": "INVALID_TEST", "elapsed": time.monotonic()-started}
        (scratch / "BeliefObservationWitness.out").write_text(output, encoding="utf-8")
        cls.receipt_path.write_text(json.dumps(cls.receipt, indent=2), encoding="utf-8")
        command = [sys.executable, str(ROOT / "verification/research/audit_belief_closure.py"),
                   "--timeout", str(timeout)]
        if pinned:
            command += ["--lean", pinned]
        try:
            run = subprocess.run(command, cwd=ROOT, capture_output=True,
                                 text=True, encoding="utf-8", timeout=timeout+30)
            output = run.stdout + run.stderr
            audit = json.loads((scratch / "receipt.json").read_text(encoding="utf-8"))
            cls.receipt["axiom_audit"] = {"status": audit["status"], "returncode": run.returncode,
                                          "declarations": audit.get("declarations", 0)}
        except (subprocess.TimeoutExpired, OSError, ValueError) as exc:
            output = str(exc)
            cls.receipt["axiom_audit"] = {"status": "INVALID_TEST"}
        (scratch / "unittest_audit.out").write_text(output, encoding="utf-8")
        changed = hashlib.sha256(fixture.read_bytes()).hexdigest() != \
            cls.receipt["source_sha256"][str(fixture.relative_to(ROOT))]
        cls.receipt["changed_during_check"] = changed
        ok = cls.receipt["fixture"]["status"] == "PASS" and \
            cls.receipt["axiom_audit"]["status"] == "PASS" and \
            cls.receipt["axiom_audit"]["returncode"] == 0 and not changed
        cls.receipt["status"] = "PASS" if ok else "FAIL"
        cls.receipt_path.write_text(json.dumps(cls.receipt, indent=2), encoding="utf-8")

    def test_actual_observation_information_boundary(self):
        self.assertEqual(self.receipt["fixture"]["status"], "PASS", str(self.receipt_path))
        self.assertFalse(self.receipt["changed_during_check"])

    def test_transitive_axioms(self):
        self.assertEqual(self.receipt["axiom_audit"]["status"], "PASS", str(self.receipt_path))
        self.assertEqual(self.receipt["axiom_audit"]["returncode"], 0)


if __name__ == "__main__":
    unittest.main()
