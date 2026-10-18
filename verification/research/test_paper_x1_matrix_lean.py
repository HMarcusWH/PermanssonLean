"""Required Research discovery checks the literal matrix adapter after the root."""

import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

import audit_x1_matrix_tables as audit
import generate_x1_matrix_tables as generator


class X1LiteralMatrixClosure(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        timeout = int(os.environ.get("PERMANSSON_X1_CHECK_TIMEOUT", "600"))
        cls.driver_run = subprocess.run([sys.executable, str(Path(audit.__file__)), "--timeout", str(timeout)],
            cwd=audit.ROOT, capture_output=True, text=True, encoding="utf-8", timeout=3*timeout+120)
        cls.path = audit.ROOT / ".lake/x1-matrix-closure/receipt.json"
        (cls.path.parent / "unittest_driver.out").write_text(cls.driver_run.stdout + cls.driver_run.stderr, encoding="utf-8")
        cls.receipt = json.loads(cls.path.read_text(encoding="utf-8"))

    def test_exact_supplied_literals(self):
        self.assertTrue(self.receipt["exact_certificate_rendering"])
        self.assertEqual(generator.TARGET.read_bytes(), generator.render().encode("utf-8"))
        self.assertEqual(self.receipt["literal_entries"], 2592)
        self.assertEqual(self.receipt["positive_control"]["status"], "PASS")

    def test_semantic_matrix_literal_rejection(self):
        result = self.receipt["mutations"].get("corrupt_matrix_literal", {})
        self.assertEqual(result.get("status"), "REJECTED", str(self.path))
        self.assertEqual(result.get("invalid_diagnostics"), [])
        self.assertTrue(result.get("expected_proof_failure"))

    def test_source_bound_transitive_audit(self):
        result = self.receipt["axiom_audit"]
        self.assertEqual(result.get("status"), "PASS", str(self.path))
        self.assertEqual(result.get("declarations"), 8)
        self.assertEqual(result.get("missing"), [])
        self.assertEqual(result.get("forbidden"), {})
        self.assertEqual(self.receipt.get("changed_files"), [])
        self.assertEqual(audit.changed_files(self.receipt["source_sha256"]), [])
        self.assertEqual(audit.changed_files(self.receipt["compiled_artifacts"]), [])
        self.assertEqual(self.driver_run.returncode, 0, str(self.path))
        self.assertEqual(self.receipt["status"], "PASS")


if __name__ == "__main__":
    unittest.main()
