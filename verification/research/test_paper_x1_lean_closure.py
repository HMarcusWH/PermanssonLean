"""Required Research CI discovers these checks AFTER building the research root.

The separate filename intentionally does not match the older pre-Lean
``test_x1*.py`` arithmetic smoke. No workflow changes are needed.
"""

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

_driver_spec = importlib.util.spec_from_file_location(
    "permansson_x1_closure_driver", Path(__file__).with_name("test_x1_paper_closure.py"))
driver = importlib.util.module_from_spec(_driver_spec)
_driver_spec.loader.exec_module(driver)


class MutationDiagnosticClassification(unittest.TestCase):
    def test_import_failure_is_invalid_even_with_later_tactic_error(self):
        output = "error: object file 'Missing.olean' of module Missing does not exist\nerror: unsolved goals"
        result = driver.classify_mutation("swapped_update_protocol", 1, output)
        self.assertEqual(result["status"], "INVALID_TEST")

    def test_parse_and_unknown_names_are_invalid(self):
        for message in ("unexpected token", "expected ':'", "unknown constant broken",
                        "unknown identifier broken", "unknown option broken"):
            with self.subTest(message=message):
                self.assertEqual(driver.classify_mutation("new_world_learning", 1,
                    f"error: {message}\nerror: unsolved goals")["status"], "INVALID_TEST")

    def test_only_expected_meaningful_failure_is_rejected(self):
        for message in ("Tactic `change` failed: target is not definitionally equal",
                        "'change' tactic failed, pattern is not definitionally equal"):
            with self.subTest(message=message):
                self.assertEqual(driver.classify_mutation("wrong_world_probability", 1,
                    f"error: {message}")["status"], "REJECTED")
        self.assertEqual(driver.classify_mutation("wrong_world_probability", 1,
            "error: unsolved goals")["status"], "UNEXPECTED_DIAGNOSTIC")
        self.assertEqual(driver.classify_mutation("wrong_world_probability", 0, "")["status"],
                         "ACCEPTED_MUTATION")

    def test_resource_failure_cannot_count_as_semantic_rejection(self):
        for message in ("maximum number of heartbeats exceeded", "allocation failed", "timeout"):
            with self.subTest(message=message):
                self.assertEqual(driver.classify_mutation("wrong_world_probability", 1,
                    f"error: {message}\nerror: Tactic `change` failed")["status"], "INVALID_TEST")

    def test_finite_semantic_failures_require_false_proposition(self):
        for name in ("wrong_terminal_horizon", "reset_before_action",
                     "omitted_minimizing_start", "corrupt_denominator"):
            with self.subTest(mutation=name):
                self.assertEqual(driver.classify_mutation(name, 1,
                    "error: Tactic `decide` proved that the proposition\n  1 = 2\nis false")["status"],
                    "REJECTED")
                self.assertEqual(driver.classify_mutation(name, 1,
                    "error: unsolved goals")["status"], "UNEXPECTED_DIAGNOSTIC")
                self.assertEqual(driver.classify_mutation(name, 1,
                    "error: unsolved goals\n⊢ False")["status"], "REJECTED")
                self.assertEqual(driver.classify_mutation(name, 1,
                    "error: Tactic `decide` failed for proposition\n"
                    "because its Decidable instance did not reduce to isTrue or isFalse")["status"],
                    "UNEXPECTED_DIAGNOSTIC")


class X1LeanClosure(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt_path = driver.ROOT / ".lake/x1-paper-closure/receipt.json"
        timeout = int(os.environ.get("PERMANSSON_X1_CHECK_TIMEOUT", "600"))
        checks = len(driver.MODULES) + len(driver.EXPECTED_PROOF_FAILURES) + 1
        command = [sys.executable, str(Path(driver.__file__).resolve()), "--timeout", str(timeout)]
        cls.driver_run = subprocess.run(command, cwd=driver.ROOT, capture_output=True, text=True,
                                 encoding="utf-8", timeout=checks*timeout+120)
        scratch = cls.receipt_path.parent
        scratch.mkdir(parents=True, exist_ok=True)
        (scratch / "unittest_driver.out").write_text(cls.driver_run.stdout + cls.driver_run.stderr, encoding="utf-8")
        cls.receipt = json.loads(cls.receipt_path.read_text(encoding="utf-8"))
        if cls.receipt.get("status") == "RUNNING":
            cls.receipt.update(status="DRIVER_ERROR", driver_returncode=cls.driver_run.returncode)
            cls.receipt_path.write_text(json.dumps(cls.receipt, indent=2), encoding="utf-8")

    def test_exact_positive_controls(self):
        controls = self.receipt["positive_controls"]
        self.assertEqual(set(controls), set(driver.MODULES))
        for name, result in controls.items():
            with self.subTest(module=name):
                self.assertEqual(result["status"], "PASS", str(self.receipt_path))

    # The historic X1 driver runs all its false probes in setUpClass. A
    # class-wide compiler observation cannot be attributed to an individual
    # original-case method. Under the PR113 trace hook, replay one additional
    # per-method SOURCE-APPENDED false equality with the actual original
    # provider as a byte-identical prefix. No ordinary driver evidence is
    # promoted or reclassified.
    _TRACE_FALSE_SOURCE = {
        "corrupt_terminal_literal": (
            "ExactTerminalTables",
            """example :
    InterventionNumerics.table false false false 0 ((0,0),false) = (1 : ℚ) := by
  exact InterventionNumerics.table_zero false false false ((0,0),false)
"""
        ),
        "wrong_terminal_horizon": (
            "ExactTerminalTables",
            """example :
    baselinePropertyValue property
      (protocolModel .equilibrium false false) ((0,0),true) =
      (InterventionNumerics.table false false false 2 ((0,0),true) : ℝ) := by
  exact original_property_eq_table .equilibrium false false ((0,0),true)
"""
        ),
        "new_world_learning": (
            "InterventionNumericalBridge",
            """example :
    (protocolModel .learner false false).inducedKernel
      ((0,0),true) {((1,1),true)} =
      ENNReal.ofReal
        (InterventionNumerics.entry false false false
          ((0,0),true) ((1,1),true) : ℝ) := by
  exact protocol_atom_eq .learner false false ((0,0),true) ((1,1),true)
"""
        ),
        "swapped_update_protocol": (
            "InterventionNumericalBridge",
            """example :
    (protocolModel .learner false true).inducedKernel
      ((0,0),true) {((1,1),true)} =
      ENNReal.ofReal
        (InterventionNumerics.entry true true false
          ((0,0),true) ((1,1),true) : ℝ) := by
  exact protocol_atom_eq .learner false true ((0,0),true) ((1,1),true)
"""
        ),
        "reset_before_action": (
            "InterventionNumericalBridge",
            """example :
    (protocolModel .learner false true).inducedKernel
      ((0,0),true) {((1,1),true)} =
      ENNReal.ofReal
        (InterventionNumerics.entry true false true
          ((1,1),true) ((1,1),true) : ℝ) := by
  exact protocol_atom_eq .learner false true ((0,0),true) ((1,1),true)
"""
        ),
    }

    def _trace_actual_false_source(self, name):
        if not os.environ.get("PR113_CAPTURE_DIR"):
            return
        if name not in self._TRACE_FALSE_SOURCE:
            return
        import tempfile
        module, assertion = self._TRACE_FALSE_SOURCE[name]
        source_file = driver.ROOT / f"PermanssonResearch/X1/{module}.lean"
        original = source_file.read_bytes()
        suffix = ("\nnamespace PermanssonResearch.X1\n" +
                  assertion + "\nend PermanssonResearch.X1\n").encode("utf-8")
        self.assertNotIn(b"\nimport ", suffix)
        self.assertNotIn(b"sorry", suffix.lower())
        self.assertNotIn(b"admit", suffix.lower())
        self.assertTrue(original)
        with tempfile.TemporaryDirectory(
                prefix="x1-method-specific-", dir=driver.ROOT / ".lake") as td:
            mutant_file = Path(td) / "FalseX1Source.lean"
            mutant_file.write_bytes(original + suffix)
            self.assertTrue(mutant_file.read_bytes().startswith(original))
            result = subprocess.run(
                ["lake", "env", "lean", str(mutant_file)],
                cwd=driver.ROOT, capture_output=True, text=True, timeout=600)
        diagnostic = (result.stdout + "\n" + result.stderr).lower()
        self.assertNotEqual(result.returncode, 0,
                            "mathematically false original-source assertion compiled")
        self.assertIn("type mismatch", diagnostic, diagnostic[-2700:])
        for bad in ("unknown identifier", "unknown module",
                    "parser error", "maximum number of heartbeats",
                    "failed to synthesize", "sorryax", "timed out"):
            self.assertNotIn(bad, diagnostic, diagnostic[-2700:])

    def _mutation(self, name):
        result = self.receipt["mutations"].get(name, {})
        self.assertEqual(result.get("status"), "REJECTED",
                         f"{name}: {result}; {self.receipt_path}")
        self.assertTrue(result.get("expected_proof_failure"))
        self.assertEqual(result.get("invalid_diagnostics"), [])
        self._trace_actual_false_source(name)

    def test_corrupt_terminal_literal(self):
        self._mutation("corrupt_terminal_literal")

    def test_wrong_world_probability(self):
        self._mutation("wrong_world_probability")

    def test_new_world_learning(self):
        self._mutation("new_world_learning")

    def test_swapped_update_protocol(self):
        self._mutation("swapped_update_protocol")

    def test_wrong_terminal_horizon(self):
        self._mutation("wrong_terminal_horizon")

    def test_reset_before_action(self):
        self._mutation("reset_before_action")

    def test_omitted_minimizing_start(self):
        self._mutation("omitted_minimizing_start")

    def test_corrupt_denominator(self):
        self._mutation("corrupt_denominator")

    def test_current_unchanged_sources_and_artifacts(self):
        self.assertEqual(self.receipt.get("receipt_version"), 2)
        self.assertEqual(self.receipt.get("changed_files"), [])
        artifacts = self.receipt.get("compiled_artifacts", {})
        self.assertEqual(len(artifacts), len(driver.MODULES))
        self.assertEqual(driver.changed_files(artifacts), [])
        self.assertEqual(driver.changed_files(self.receipt["source_sha256"]), [])
        self.assertEqual(driver.changed_files(self.receipt["verification_sha256"]), [])
        for name, result in self.receipt["positive_controls"].items():
            with self.subTest(module=name):
                self.assertEqual(result["control_sha256"],
                    self.receipt["source_sha256"][f"PermanssonResearch/X1/{name}.lean"])

    def test_transitive_axioms(self):
        audit = self.receipt["axiom_audit"]
        self.assertEqual(audit.get("status"), "PASS", str(self.receipt_path))
        self.assertGreaterEqual(audit.get("declarations", 0), 57)
        self.assertEqual(audit.get("missing"), [])
        self.assertEqual(audit.get("forbidden"), {})

    def test_complete_validated_receipt(self):
        self.assertEqual(self.driver_run.returncode, 0, str(self.receipt_path))
        self.assertEqual(self.receipt["status"], "PASS")
        self.assertEqual(set(self.receipt["mutations"]), set(driver.EXPECTED_PROOF_FAILURES))


if __name__ == "__main__":
    unittest.main()
