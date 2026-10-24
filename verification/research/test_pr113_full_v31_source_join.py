"""Synthetic-only R08 full source join adversaries; no external approvals."""
import copy
import unittest

from pr113_full_v31_source_join import (
    CombinedEvidenceError, join_authenticated_evidence,
)


H = "a" * 40
S = "b" * 40
CLAIMS = ("Q1", "Q2", "Q3", "M1", "M2", "M3", "N1", "N2", "N3", "D8", "D9")


def complete():
    v3 = {
        "status": "COMPLETE_SOURCE_EVIDENCE_UNREVIEWED_NOT_ACCEPTED",
        "candidate_controls_complete": True, "source_proofs": 259,
        "producer_shards": 21, "exact_head_required_ci": 12,
        "actual_github_producer_shards": 21,
        "cases_with_positive_negative_controls": 45,
        "claims_with_positive_negative_controls": 11,
        "independent_case_reviews": 0, "independent_claim_reviews": 0,
        "source_head": H, "synthetic_sha": S,
    }
    owners = ([{"kind": "original_positive", "owner_id": f"C-{i:02}"}
               for i in range(1, 46)] +
              [{"kind": "legacy_negative", "owner_id": f"C-{i:02}"}
               for i in range(1, 21)] +
              [{"kind": "claim_pair", "owner_id": x} for x in CLAIMS])
    v31 = {
        "format": "Permansson.PR113.ControlCIAuthenticationCandidate.v3.1",
        "status": "ALL_ADDITIONAL_CONTROLS_SOURCE_ATTRIBUTED_UNREVIEWED",
        "head_sha": H,
        "original_21_producing_artifacts_still_required": 21,
        "original_case_positives": 45,
        "legacy_case_negatives": 20,
        "claim_positive_negative_pairs": 11,
        "accepted_cases": 0, "accepted_claims": 0,
        "schema_security_approved": False,
        "independent_mathematical_review": False,
        "full_release_approved": False,
        "source_owned_controls": owners,
        "actual_execution_member_validation": {
            "format": "Permansson.PR113.GenuineSourceExecutionBytes.v1",
            "status": "ACTUAL_CONTROL_BYTES_REVALIDATED_UNREVIEWED",
            "source_head": H, "source_owner_count": 76,
            "claim_positive_negative_directions": 22,
            "execution_log_members_checked": 208,
            "independent_review": False,
            "mathematical_acceptance": False,
            "publication_approved": False,
        },
    }
    return v3, v31


class FullSourceJoinTests(unittest.TestCase):
    def test_complete_mock_graph_never_claims_release(self):
        a, b = complete()
        r = join_authenticated_evidence(a, b)
        self.assertEqual(r["kernel_theorem_receipts"], 259)
        self.assertEqual(r["additional_gh_source_owner_records"], 76)
        self.assertFalse(r["independent_review"])
        self.assertFalse(r["security_approval"])
        self.assertFalse(r["publication_authorized"])
        self.assertFalse(r["merge_authorized"])

    def test_missing_original_required_ci_or_proof_is_blocked(self):
        for key, n in (("original_ci_checks", 11), ("source_proofs", 258),
                       ("cases_with_positive_negative_controls", 44),
                       ("claims_with_positive_negative_controls", 10)):
            a, b = complete()
            if key == "original_ci_checks":
                a["exact_head_required_ci"] = 11
            else:
                a[key] = n
            with self.subTest(key=key), self.assertRaises(CombinedEvidenceError):
                join_authenticated_evidence(a, b)

    def test_v31_75_owners_or_stale_head_blocks(self):
        a, b = complete()
        b["source_owned_controls"].pop()
        with self.assertRaises(CombinedEvidenceError):
            join_authenticated_evidence(a, b)
        a, b = complete()
        b["head_sha"] = "c" * 40
        with self.assertRaises(CombinedEvidenceError):
            join_authenticated_evidence(a, b)

    def test_fake_source_and_missing_negative_direction_block(self):
        a, b = complete()
        b["actual_execution_member_validation"]["execution_log_members_checked"] = 0
        with self.assertRaises(CombinedEvidenceError):
            join_authenticated_evidence(a, b)
        a, b = complete()
        b["actual_execution_member_validation"]["claim_positive_negative_directions"] = 11
        with self.assertRaises(CombinedEvidenceError):
            join_authenticated_evidence(a, b)

    def test_unreviewed_status_cannot_be_replaced_with_approval(self):
        a, b = complete()
        b["schema_security_approved"] = True
        with self.assertRaises(CombinedEvidenceError):
            join_authenticated_evidence(a, b)
        a, b = complete()
        b["actual_execution_member_validation"]["mathematical_acceptance"] = True
        with self.assertRaises(CombinedEvidenceError):
            join_authenticated_evidence(a, b)

    def test_duplicate_or_wrong_kind_fails(self):
        a, b = complete()
        b["source_owned_controls"][3] = b["source_owned_controls"][2].copy()
        with self.assertRaises(CombinedEvidenceError):
            join_authenticated_evidence(a, b)
        a, b = complete()
        b["source_owned_controls"][0]["kind"] = "claim_pair"
        with self.assertRaises(CombinedEvidenceError):
            join_authenticated_evidence(a, b)


if __name__ == "__main__":
    unittest.main()
