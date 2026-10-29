"""Adversarial, Python-only tests for original 45-case route preparation."""
import hashlib
import unittest

from pr113_prepare_positive_selection import (
    SelectionError, choose_role, derive, method_class, FORMAT,
)


TEST_PATH = "verification/research/test_fixture.py"
PROOF_PATH = "PermanssonResearch/Fixture.lean"
TEST = b"""import unittest
class Legitimate(unittest.TestCase):
    def test_valid(self):
        self.assertTrue(True)
"""
PROOF = b"theorem actual_fact : True := by trivial\n"


def original_case(number, route="COMPILER_SOURCE"):
    return {
        "case_id": f"Z-{number:02d}",
        "test_method_candidates": [{
            "path": TEST_PATH,
            "method": "test_valid",
            "role": route,
        }],
        "historical_proof_declarations": [{
            "path": PROOF_PATH,
            "name": "actual_fact",
        }],
    }


class OriginalPositiveSelectionTests(unittest.TestCase):
    def test_exact_45_distinct_source_selected_but_unapproved(self):
        source_map = {"cases": [original_case(i) for i in range(45)]}
        def original(_head, path):
            return {TEST_PATH: TEST, PROOF_PATH: PROOF}[path]
        selection, review = derive("a" * 40, source_map, original)
        self.assertEqual(selection["format"], FORMAT)
        self.assertEqual(len(selection["cases"]), 45)
        self.assertEqual(set(row["test_class"] for row in selection["cases"]),
                         {"Legitimate"})
        self.assertEqual(set(row["proof_source_path"] for row
                             in selection["cases"]), {PROOF_PATH})
        self.assertEqual(review["selected_case_count"], 45)
        self.assertFalse(review["reviewed"])
        self.assertFalse(review["executed"])
        self.assertEqual(review["accepted_cases"], 0)
        self.assertEqual(review["source_sha256"][PROOF_PATH],
                         hashlib.sha256(PROOF).hexdigest())

    def test_missing_one_original_is_not_completed(self):
        with self.assertRaises(SelectionError):
            derive("a" * 40,
                   {"cases": [original_case(i) for i in range(44)]},
                   lambda _h, p: TEST)

    def test_duplicate_original_is_rejected(self):
        cases = [original_case(i) for i in range(44)]
        cases.append(original_case(4))
        with self.assertRaisesRegex(SelectionError, "duplicate"):
            derive("a" * 40, {"cases": cases},
                   lambda _h, p: TEST)

    def test_semantic_negative_cannot_be_used_as_positive(self):
        with self.assertRaisesRegex(SelectionError, "source-positive"):
            choose_role(original_case(1, route="SEMANTIC_NEGATIVE"))

    def test_compiler_route_preferred_over_exact_check(self):
        case = original_case(1, route="EXACT_CHECK")
        case["test_method_candidates"].append({
            "path": TEST_PATH, "method": "test_valid",
            "role": "COMPILER_SOURCE",
        })
        self.assertEqual(choose_role(case)["role"], "COMPILER_SOURCE")

    def test_unique_original_unittest_class_is_required(self):
        self.assertEqual(method_class(TEST, "test_valid"), "Legitimate")
        with self.assertRaises(SelectionError):
            method_class(TEST, "test_does_not_exist")
        ambiguous = TEST + b"""class Extra(unittest.TestCase):
    def test_valid(self):
        pass
"""
        with self.assertRaisesRegex(SelectionError, "unique"):
            method_class(ambiguous, "test_valid")

    def test_case_with_no_actual_proof_provider_cannot_be_selected(self):
        cases = [original_case(i) for i in range(45)]
        cases[5]["historical_proof_declarations"] = []
        with self.assertRaisesRegex(SelectionError, "provider"):
            derive("a" * 40, {"cases": cases},
                   lambda _h, p: TEST)


if __name__ == "__main__":
    unittest.main()
