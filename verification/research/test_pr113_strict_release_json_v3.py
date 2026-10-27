"""New external scholarly/producer input JSON is never last-key-wins.

These fixtures are not GitHub identity, theorem or independent review evidence.
"""
import tempfile
from pathlib import Path
import unittest
from unittest import mock

import final_closure_gate as gate
import final_closure_verify as verification


class StrictInputBoundaryTests(unittest.TestCase):
    def test_duplicate_source_case_decision_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            record=Path(temp)/"cases.json"
            record.write_bytes(
                b'{"case_id":"X-01","decision":"PENDING",'
                b'"decision":"VERIFIED_SELECTED_SCOPE"}')
            with self.assertRaises(ValueError):
                verification.read_json(record)

    def test_duplicate_detached_receipt_stops_before_github_review(self):
        with tempfile.TemporaryDirectory() as temp:
            receipts=Path(temp)/"receipts.json"
            bundle=Path(temp)/"evidence.zip"
            receipts.write_bytes(
                b'{"format":"Permansson.FinalClosureDetachedReceipts.v3",'
                b'"format":"REVIEW_ALREADY_ACCEPTED"}')
            bundle.write_bytes(b"PK_fake_unreviewed")
            with mock.patch.object(gate, "premerge") as authenticate:
                result=gate.main([
                    "--phase","premerge","--receipts",str(receipts),
                    "--bundle",str(bundle)])
            self.assertEqual(result,2)
            authenticate.assert_not_called()

    def test_malformed_nonfinite_premerge_source_fails_closed(self):
        with tempfile.TemporaryDirectory() as temp:
            receipts=Path(temp)/"receipts.json"
            bundle=Path(temp)/"evidence.zip"
            receipts.write_bytes(b'{"value": NaN}')
            bundle.write_bytes(b"PK_fake")
            with mock.patch.object(gate, "premerge") as authenticate:
                self.assertEqual(gate.main([
                    "--phase","premerge","--receipts",str(receipts),
                    "--bundle",str(bundle)]),2)
            authenticate.assert_not_called()


if __name__ == "__main__":
    unittest.main()
