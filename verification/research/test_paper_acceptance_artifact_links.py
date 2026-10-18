"""Check the published ledger's durable evidence links after Git checkout.

Local provider/artifact hashes describe their measured environment. These
checks instead authenticate the portable receipt and raw-log bytes that the
ledger actually publishes, independently of Windows text conversion.
"""
import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'research/paper_closures'


def load(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))


class PublishedAcceptanceArtifacts(unittest.TestCase):
    def assert_bound_file(self, relative, expected):
        path = ROOT / relative
        self.assertTrue(path.is_file(), relative)
        self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), expected, relative)

    def test_all_supplied_cases_have_local_evidence(self):
        ledger = load(OUT/'acceptance_evidence.json')
        supplied = load(OUT/'spec/registries/acceptance_tests.json')
        rows = supplied['cases']
        self.assertEqual({row['id'] for row in ledger['cases']}, {row['id'] for row in rows})
        self.assertEqual(ledger['status_counts'], {'LOCAL_EVIDENCE_COMPLETE':45})
        self.assertEqual(ledger['case_count'], 45)
        self.assertIsNone(ledger['eventual_merge_M'])

    def test_receipt_links_bind_published_raw_bytes(self):
        ledger = load(OUT/'acceptance_evidence.json')
        self.assert_bound_file(ledger['registry']['path'], ledger['registry']['sha256'])
        for row in ledger['receipt_inventory']:
            with self.subTest(receipt=row['path']):
                self.assertFalse(row['path'].startswith('.lake/'))
                self.assert_bound_file(row['path'], row['sha256'])
        for case in ledger['cases']:
            for proof in case['proofs']:
                for receipt in proof.get('current_source_bound_receipts', []):
                    self.assert_bound_file(receipt['path'], receipt['sha256'])

    def test_preserved_owner_receipts_and_audit_logs(self):
        inventory = load(OUT/'acceptance_raw_evidence_inventory.json')
        self.assertEqual(inventory['status'], 'PASS')
        for row in inventory['durable_owner_receipts']:
            self.assert_bound_file(row['durable'], row['sha256'])
            self.assertEqual(load(ROOT/row['durable']), load(ROOT/row['owner_path']))
        for row in inventory['audits']:
            self.assert_bound_file(row['receipt'], row['receipt_sha256'])
            for key in ['audit_source', 'audit_stdout']:
                record = row[key]
                self.assert_bound_file(record['durable'], record['sha256'])


if __name__ == '__main__':
    unittest.main()
