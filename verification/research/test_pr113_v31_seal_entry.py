"""Full-release sealer CLI must pass actual v3.1 auth input, never flags."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

RELEASE = Path(__file__).resolve().parents[2] / "release/mathematical-closure-1"
if str(RELEASE) not in sys.path:
    sys.path.insert(0, str(RELEASE))
import seal_approved as seal


class SourceControlledFullSealingTests(unittest.TestCase):
    def test_full_candidate_cli_rejects_missing_76_control_inputs(self):
        with tempfile.TemporaryDirectory(prefix="perm-v31-seal-") as td:
            root = Path(td)
            approved = root / "approved.json"
            receipts = root / "receipts.json"
            approved.write_text("{}")
            receipts.write_text("{}")
            argv = [
                "--draft-dir", str(root / "draft"),
                "--approved-claim-manifest", str(approved),
                "--source-receipts", str(receipts),
                "--bundle", str(root / "nonexistent-evidence.zip"),
                "--out", str(root / "candidate"),
                "--full",
            ]
            with mock.patch.object(seal, "seal") as strict:
                self.assertEqual(seal.main(argv), 2)
                strict.assert_not_called()

    def test_full_sealing_forwards_real_v31_source_inputs_to_strict_gate(self):
        with tempfile.TemporaryDirectory(prefix="perm-v31-seal-") as td:
            base = Path(td)
            draft = base / "draft"
            draft.mkdir()
            three = {
                "additional_contract": base / "contract.json",
                "additional_zips": base / "original-real-gh-zips",
                "workflow_blob_candidates": base / "workflow-oid-candidates.json",
            }
            def blocked(*args, **kwargs):
                self.assertEqual(args[1], "postmerge-preseal-strict")
                self.assertEqual(kwargs.get("v31_attachment"), three)
                raise seal.SealError("MOCK ONLY: no real GitHub security review")
            with mock.patch.object(seal.draft_verifier, "verify",
                                   return_value={"integrity": "PASS"}), \
                 mock.patch.object(seal, "prepare_approved_manifest",
                                   return_value=({}, {})), \
                 mock.patch.object(seal, "strict_acceptance",
                                   side_effect=blocked) as strict:
                with self.assertRaisesRegex(seal.SealError, "MOCK ONLY"):
                    seal.seal(draft, {}, {}, base / "original-bundle.zip",
                              base / "candidate", full=True,
                              v31_attachment=three)
                strict.assert_called_once()
            self.assertFalse((base / "candidate").exists())


if __name__ == "__main__":
    unittest.main()
