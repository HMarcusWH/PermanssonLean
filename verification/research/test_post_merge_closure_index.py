"""PR79 source/CI evidence acceptance, separate from the A2-P02 mathematical PR.

Intentionally do not skip Git byte checks on CI; this does not promote
historical receipt or an unverified human review into mathematical proof.
"""
from copy import deepcopy
from pathlib import Path
import unittest
from post_merge_closure_index import (
    EvidenceError, read_bundle, verify_index, release_gate, git_object,
    old_newline_variant, strict_json, MERGE, TREE, PATH,
)

ROOT=Path(__file__).resolve().parents[2]

class PostMergeClosureIndexTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.index,cls.norm,cls.decision=read_bundle(ROOT)

    def check(self, index=None, norm=None, decision=None, **kwargs):
        return verify_index(index or self.index, norm or self.norm,
                            decision or self.decision, **kwargs)

    def test_42_contract_45_acceptance_complete_and_nonrelease(self):
        result=self.check()
        self.assertEqual(result['contracts'],42)
        self.assertEqual(result['acceptance_cases'],45)
        self.assertEqual(result['owner_records'],256)
        self.assertGreater(len(result['pending_cases']),0)
        self.assertFalse(result['release_ready'])

    def test_actual_merged_source_bytes_and_git_commit(self):
        result=self.check(source_reader=lambda path:git_object(ROOT, f'{MERGE}:{path}'),
                          commit_reader=lambda sha:git_object(ROOT,sha))
        self.assertEqual(result['source_rows_checked'],256)
        self.assertEqual(result['source_tree'], TREE)

    def test_release_gate_is_fail_closed_for_historical_acceptance(self):
        with self.assertRaisesRegex(EvidenceError,'RELEASE BLOCKED'):
            release_gate(self.check())

    def test_wrong_merge_parent_or_source_identity_rejected(self):
        candidate=deepcopy(self.index)
        candidate['reference']['M_parent_order']=['H','B']
        with self.assertRaisesRegex(EvidenceError,'parent order'):
            self.check(index=candidate)
        candidate=deepcopy(self.index)
        candidate['CI']['PR79_source_head'][0]['head_sha']='0'*40
        with self.assertRaisesRegex(EvidenceError,'wrong source'):
            self.check(index=candidate)

    def test_unaudited_declared_review_is_rejected(self):
        candidate=deepcopy(self.index)
        candidate['review_status']='EXTERNAL_REVIEW_APPROVED'
        with self.assertRaisesRegex(EvidenceError,'review falsely promoted'):
            self.check(index=candidate)

    def test_invalid_claimed_census_cannot_be_approval(self):
        candidate=deepcopy(self.index)
        candidate['claimed_17_check_679_reference_census']='VERIFIED'
        with self.assertRaisesRegex(EvidenceError,'census promoted'):
            self.check(index=candidate)

    def test_pending_partial_rows_cannot_be_silently_accepted(self):
        candidate=deepcopy(self.decision)
        candidate['pending_ids']=[]
        with self.assertRaisesRegex(EvidenceError,'pending case'):
            self.check(decision=candidate)
        candidate=deepcopy(self.decision)
        candidate['full_selected_programme_accepted']=True
        with self.assertRaisesRegex(EvidenceError,'false full acceptance'):
            self.check(decision=candidate)

    def test_owner_digest_cannot_be_repaired_by_claim(self):
        candidate=deepcopy(self.norm)
        candidate['historical_mismatch_disposition']['status']='RECONCILED'
        with self.assertRaisesRegex(EvidenceError,'unresolved digest promoted'):
            self.check(norm=candidate)
        candidate=deepcopy(self.decision)
        candidate['unverified_owner_digest_retired_from_authority']=False
        with self.assertRaisesRegex(EvidenceError,'owner digest promotion'):
            self.check(decision=candidate)

    def test_correct_newline_maps_do_not_mutate_canonical_source(self):
        source=b'first\nsecond\n'
        self.assertEqual(old_newline_variant(source,'RAW'),source)
        self.assertEqual(old_newline_variant(source,'CRLF'),b'first\r\nsecond\r\n')
        self.assertEqual(old_newline_variant(source,'LF_FINAL_CRLF'),b'first\nsecond\r\n')
        self.assertEqual(old_newline_variant(source,'LF_FINAL_TWO_CRLF'),b'first\r\nsecond\r\n')
        with self.assertRaises(EvidenceError):
            old_newline_variant(source,'UNKNOWN')

    def test_canonical_source_guard_catches_false_digest(self):
        with self.assertRaisesRegex(EvidenceError,'canonical Git source mismatch'):
            self.check(source_reader=lambda path:b'fabricated source bytes')

    def test_duplicate_json_key_rejected(self):
        with self.assertRaisesRegex(EvidenceError,'duplicate JSON key'):
            strict_json(b'{"a":1,"a":2}')

    def test_missing_declaration_and_assumption_routing_rejected(self):
        candidate=deepcopy(self.index)
        candidate['contracts'][0]['acceptance_ids']=[]
        # X-01 is also routed by other contracts, so delete all occurrences.
        for c in candidate['contracts']:
            c['acceptance_ids']=[i for i in c['acceptance_ids'] if i!='X-01']
        with self.assertRaisesRegex(EvidenceError,'acceptance routing'):
            self.check(index=candidate)

if __name__=='__main__': unittest.main()
