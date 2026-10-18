"""Discovered integration checks for the actual nonperiodic natural clock."""
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
import audit_nat_private_clock as audit


class NatPrivateClockClosure(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        timeout = int(os.environ.get("PERMANSSON_X1_CHECK_TIMEOUT", "600"))
        cls.driver_run = subprocess.run([sys.executable, str(Path(audit.__file__)), "--timeout", str(timeout)],
            cwd=audit.ROOT, capture_output=True, text=True, encoding="utf-8", timeout=5*timeout+120)
        cls.path = audit.ROOT / ".lake/nat-private-clock-closure/receipt.json"
        (cls.path.parent / "unittest_driver.out").write_text(cls.driver_run.stdout + cls.driver_run.stderr, encoding="utf-8")
        cls.receipt = json.loads(cls.path.read_text(encoding="utf-8"))

    def test_actual_nonperiodic_natural_clock(self):
        self.assertEqual(set(self.receipt["positive_controls"]), set(audit.MODULES) | {"fixture"})
        for result in self.receipt["positive_controls"].values():
            self.assertEqual(result["status"], "PASS", str(self.path))

    def test_frozen_clock_semantic_rejection(self):
        result = self.receipt["mutations"].get("frozen_clock", {})
        self.assertEqual(result.get("status"), "REJECTED", str(self.path))
        self.assertEqual(result.get("invalid_diagnostics"), [])
        self.assertTrue(result.get("expected_proof_failure"))

    def test_source_bound_axioms(self):
        result = self.receipt["axiom_audit"]
        self.assertEqual(result.get("status"), "PASS", str(self.path))
        self.assertGreater(result.get("declarations", 0), 30)
        self.assertEqual(result.get("missing"), [])
        self.assertEqual(result.get("forbidden"), {})
        self.assertEqual(self.receipt.get("changed_files"), [])
        self.assertEqual(audit.changed_files(self.receipt["source_sha256"]), [])
        self.assertEqual(audit.changed_files(self.receipt["compiled_artifacts"]), [])
        self.assertEqual(self.driver_run.returncode, 0, str(self.path))
        self.assertEqual(self.receipt["status"], "PASS")


if __name__ == "__main__":
    unittest.main()
