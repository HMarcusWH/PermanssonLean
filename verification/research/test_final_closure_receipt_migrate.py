"""Legacy labels never become independent acceptance by migration."""
import unittest
import final_closure_receipt_migrate as m


class LegacyReceiptTests(unittest.TestCase):
    def test_old_axiom_allowlist_never_becomes_observed_transitive_axioms(self):
        old = {
            "declaration": "Example.theorem",
            "path": "PermanssonResearch/Example.lean",
            "reviewed_head_sha": "a"*40,
            "source_sha256": "b"*64,
            "statement_sha256": "c"*64,
            "axiom_allowlist": ["propext", "Classical.choice"],
            "compiler_run_url": "https://example.com/fake",
            "compiler_result": "PASS", "reviewer_signoff": True,
        }
        r = m.statement_candidate(old)
        self.assertIsNone(r["transitive_axioms"])
        self.assertEqual(r["compiler_result"], "NOT_VERIFIED")
        self.assertIsNone(r["check_run_id"])
        self.assertEqual(r["independent_review_receipts"], [])

    def test_legacy_source_ci_ids_must_be_reauthenticated(self):
        old = {
            "base_sha": "a"*40,
            "head_sha": "b"*40,
            "merged_main_sha": "c"*40,
            "source_ci_receipts": [{"name": "research", "id": 777}],
            "authenticated": True,
        }
        r = m.source_receipt_candidate(old)
        self.assertEqual(r["source_bound_ci"], [])
        self.assertEqual(r["independent_source_reviews"], [])
        self.assertNotEqual(r["format"], "Permansson.FinalClosureDetachedReceipts.v2")

    def test_missing_bytes_cannot_migrate_to_verified_receipts(self):
        with self.assertRaises(m.MigrationError):
            m.statement_candidate({"declaration":"Fake.theorem",
                                   "compiler_result":"PASS"})


if __name__ == "__main__":
    unittest.main()
