"""Pure contract tests for individual X1 source-appended Lean false probes.

These tests do not pretend that a source-string test is a Lean compiler
certificate. The compiler and independent CI producer remain mandatory.
"""
import json
from pathlib import Path
import unittest

import test_paper_x1_lean_closure as trace

ROOT = Path(__file__).resolve().parents[2]
CASE_MAP = ROOT / "research/paper_closures/post_merge_112/acceptance_case_source_map.json"
CASES = {"X-02": {"test_corrupt_terminal_literal",
                  "test_wrong_terminal_horizon"},
         "X-05": {"test_reset_before_action",
                  "test_new_world_learning",
                  "test_swapped_update_protocol"}}


class OriginalX1MethodTraceContract(unittest.TestCase):
    def test_exact_case_method_selection_matches_original_registry(self):
        registered = json.loads(CASE_MAP.read_text(encoding="utf-8"))["cases"]
        by_id = {row["case_id"]: row for row in registered}
        for case_id, expected in CASES.items():
            methods = {row["method"] for row in
                       by_id[case_id]["test_method_candidates"]
                       if row["role"] == "SEMANTIC_NEGATIVE"}
            self.assertEqual(methods, expected)
        expected_methods = set().union(*CASES.values())
        mapped = trace.X1LeanClosure._TRACE_FALSE_SOURCE
        self.assertEqual(set(mapped), {
            "corrupt_terminal_literal", "wrong_terminal_horizon",
            "reset_before_action", "new_world_learning",
            "swapped_update_protocol"})
        self.assertEqual({"test_" + name for name in mapped}, expected_methods)

    def test_each_probe_preserves_declared_original_provider_and_false_goal(self):
        mapped = trace.X1LeanClosure._TRACE_FALSE_SOURCE
        self.assertEqual(len(mapped), 5)
        for name, (module, statement) in mapped.items():
            with self.subTest(name=name):
                self.assertIn(module, trace.driver.MODULES)
                src = ROOT / f"PermanssonResearch/X1/{module}.lean"
                self.assertTrue(src.is_file())
                original = src.read_bytes()
                suffix = ("\nnamespace PermanssonResearch.X1\n" +
                          "open PermanssonLean PermanssonLean.RegimeSpecification\n" +
                          statement + "\nend PermanssonResearch.X1\n").encode("utf-8")
                self.assertTrue((original + suffix).startswith(original))
                self.assertIn(" := by\n  exact ", statement)
                self.assertFalse(any(x in suffix for x in (
                    b"\nimport ", b"sorry", b"admit", b"axiom ")))
                self.assertLess(len(suffix), 16 * 1024)

    def test_unexecuted_string_inspection_has_no_acceptance_status(self):
        # Preserve the separation of source candidates from real producing
        # compiler log, reviewer decision and original-case acceptance.
        self.assertTrue(CASES)
        self.assertFalse(hasattr(trace.X1LeanClosure, "independent_case_approval"))


if __name__ == "__main__":
    unittest.main()
