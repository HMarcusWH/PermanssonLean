"""Exact selected-scope inventory obligations; synthetic rows are NEVER proofs."""
import copy
import unittest
from final_closure_complete_lean_evidence import (
    FULL_TARGET_COUNT, FROZEN_CLAIM_IDS,
    CompleteCompilerError, validate_full_release_inventory,
)


def synthetic_inventory():
    claims = sorted(FROZEN_CLAIM_IDS)
    return [
        {
            "path": f"PermanssonResearch/Fake/F{n:03}.lean",
            "declaration": f"PermanssonResearch.Fake.t{n:03}",
            "case_ids": [f"C-{(n % 45) + 1:02}"],
            "claim_ids": [claims[n % len(claims)]],
        }
        for n in range(FULL_TARGET_COUNT)
    ]


class FullReleaseInventoryScopeTests(unittest.TestCase):
    def test_exact_259_originals_are_only_candidate_inventory(self):
        rows = synthetic_inventory()
        self.assertEqual(len(validate_full_release_inventory(rows)), 259)

    def test_258_successful_theorems_are_incomplete(self):
        rows = synthetic_inventory()
        rows.pop()
        with self.assertRaisesRegex(CompleteCompilerError, "259"):
            validate_full_release_inventory(rows)

    def test_duplicate_theorem_is_not_two_proof_receipts(self):
        rows = synthetic_inventory()
        rows[22] = copy.deepcopy(rows[21])
        with self.assertRaisesRegex(CompleteCompilerError, "duplicate"):
            validate_full_release_inventory(rows)

    def test_duplicate_fqn_in_other_file_is_rejected(self):
        rows = synthetic_inventory()
        rows[22]["declaration"] = rows[21]["declaration"]
        with self.assertRaisesRegex(CompleteCompilerError, "duplicate"):
            validate_full_release_inventory(rows)

    def test_claim_or_case_omission_is_not_full_completion(self):
        rows = synthetic_inventory()
        for row in rows:
            row["claim_ids"] = ["Q1"]
        with self.assertRaisesRegex(CompleteCompilerError, "45/11"):
            validate_full_release_inventory(rows)
        rows = synthetic_inventory()
        for row in rows:
            row["case_ids"] = ["C-01"]
        with self.assertRaisesRegex(CompleteCompilerError, "45/11"):
            validate_full_release_inventory(rows)

    def test_foreign_claim_and_missing_source_owner_rejected(self):
        rows = synthetic_inventory()
        rows[0]["claim_ids"].append("UNAPPROVED")
        with self.assertRaises(CompleteCompilerError):
            validate_full_release_inventory(rows)
        rows = synthetic_inventory()
        rows[0]["path"] = "../shadow/NotProof.lean"
        with self.assertRaises(CompleteCompilerError):
            validate_full_release_inventory(rows)
        rows = synthetic_inventory()
        rows[0]["case_ids"] = []
        rows[0]["claim_ids"] = []
        with self.assertRaises(CompleteCompilerError):
            validate_full_release_inventory(rows)


if __name__ == "__main__":
    unittest.main()
