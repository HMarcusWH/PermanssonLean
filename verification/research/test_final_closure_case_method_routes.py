"""Scope-route smoke/adversarial checks: 45 selected IDs are NOT acceptance."""
from __future__ import annotations

import copy
import unittest

import final_closure_case_method_routes as routes
import final_closure_case_map as cases


class OriginalMethodRoutes(unittest.TestCase):
    def test_all_45_current_test_methods_resolve(self):
        source = cases.generate()
        rows = source["cases"]
        self.assertEqual(len(rows), 45)
        self.assertEqual(len({r["case_id"] for r in rows}), 45)
        self.assertTrue(all(r["test_source_candidates"] and
                            r["test_method_candidates"] and
                            r["effective_accepted"] is False
                            for r in rows))
        self.assertEqual(sum(len(r["test_method_candidates"]) for r in rows), 154)
        self.assertEqual(source["status"], "UNREVIEWED_CANDIDATE_ONLY")
        selected = routes.validated_routes([r["case_id"] for r in rows])
        for row in rows:
            self.assertEqual(selected[row["case_id"]],
                             row["test_method_candidates"])
            self.assertEqual(row["case_specific_test_status"],
                             "CANDIDATES_REQUIRE_CRITERION_RELEVANCE_REVIEW")
            self.assertFalse(any("review_id" in candidate for candidate
                                 in row["test_method_candidates"]))
            self.assertTrue(all(c["status"] ==
                                "DISCOVERED_UNREVIEWED_NOT_EXECUTION_EVIDENCE"
                                for c in row["test_method_candidates"]))

    def test_missing_or_extra_case_rejected(self):
        ids = list(routes.METHOD_ROUTES)
        for changed in (ids[:-1], ids + ["X-999"], ids[:-1] + [ids[0]]):
            with self.subTest(changed=len(changed)), self.assertRaises(ValueError):
                routes.validated_routes(changed)

    def test_wrong_method_and_wrong_role_rejected(self):
        ids = list(routes.METHOD_ROUTES)
        for fault in ("missing_method", "wrong_role", "duplicate"):
            bad = copy.deepcopy(routes.METHOD_ROUTES)
            original = bad["X-02"][0]
            if fault == "missing_method":
                original[1] = "test_aliased_nonexistent_proof"
            elif fault == "wrong_role":
                original[2] = "APPROVED_BY_CI"
            else:
                bad["X-02"].append(original[:])
            with self.subTest(fault=fault), self.assertRaises(ValueError):
                routes.validated_routes(ids, routes=bad)

    def test_preserved_original_case_wording(self):
        source = cases.generate()
        old = cases.json.loads((cases.SNAP / "acceptance_decisions.json").read_text())
        for historical, selected in zip(old["cases"], source["cases"]):
            self.assertEqual(historical["required_expected_result"],
                             selected["required_expected_result"])
            self.assertEqual(historical["historical_contract_ids"],
                             selected["historical_contract_ids"])
            self.assertEqual(historical["proof_declarations"],
                             selected["historical_proof_declarations"])

    def test_b02_uses_specific_minimality_negative_not_only_d08(self):
        row = next(c for c in cases.generate()["cases"] if c["case_id"] == "B-02")
        self.assertTrue(any(c["method"] == "test_10_XOR_destroys_upward_monotonicity"
                            for c in row["test_method_candidates"]))
        self.assertFalse(row["effective_accepted"])


if __name__ == "__main__":
    unittest.main()
