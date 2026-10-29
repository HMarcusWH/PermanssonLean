"""Single-PR candidate acceptance must never masquerade as final review."""
import copy
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "verification/research"))
import final_closure_verify as gate


class FinalClosureAcceptanceTests(unittest.TestCase):
    def test_candidate_inventory_is_full_but_pending(self):
        result = gate.audit()
        self.assertEqual(result["cases"], 45)
        self.assertEqual(result["contracts"], 42)
        self.assertEqual(result["closures"], 11)
        self.assertGreater(result["pending"], 0)

    def test_full45_without_real_source_receipts_rejects(self):
        with self.assertRaises(gate.GateError):
            gate.strict({}, "full45-strict", None)

    def test_scoped_release_needs_authenticated_compiler_and_review(self):
        with self.assertRaises(gate.GateError):
            gate.strict({"authenticated": True}, "scoped-release-strict",
                        {"status": "APPROVED_SOURCE_BOUND"})

    def test_historical_expectations_remain_complete(self):
        hist = gate.read_json(gate.OLD / "acceptance_decisions.json")
        snap = gate.read_json(gate.NEW / "acceptance_decisions.json")
        byid = {c["id"]: c for c in hist["cases"]}
        for case in snap["cases"]:
            self.assertEqual(case["required_expected_result"],
                             byid[case["case_id"]]["required_expected_result"])


if __name__ == "__main__":
    unittest.main()
