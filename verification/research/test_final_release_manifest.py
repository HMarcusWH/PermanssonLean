"""No incomplete draft may masquerade as a mathematical release."""
import json,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"release/mathematical-closure-1"))
import verify_release as vr

class CandidateReleaseTests(unittest.TestCase):
    def test_unreviewed_manifest_is_still_draft(self):
        obj=json.loads((ROOT/"release/mathematical-closure-1/manifest.json").read_text())
        self.assertEqual(obj["status"],"DRAFT_NOT_ACCEPTED")
        self.assertIsNone(obj["source_commit_sha"])
        self.assertFalse(obj["approved_manuscript_claims"])
    def test_fake_receipt_with_no_pdf_is_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t)/"manifest.lock.json"
            p.write_text(json.dumps({"format":"Permansson.MathClosure.BuildReceipt.v1",
              "mode":"DRAFT","empirical_identification_status":"NOT_ESTABLISHED",
              "pdf_sha256":"0"*64,"tex_sha256":"1"*64,
              "latex_log_sha256":"2"*64}))
            with self.assertRaises(ValueError): vr.verify(p)
    def test_strict_rejects_draft(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t)/"manifest.lock.json"
            p.write_text(json.dumps({"format":"Permansson.MathClosure.BuildReceipt.v1",
              "mode":"DRAFT","status":"DRAFT_NOT_ACCEPTED",
              "empirical_identification_status":"NOT_ESTABLISHED"}))
            with self.assertRaises((KeyError,ValueError)): vr.verify(p,strict=True)
if __name__=="__main__":unittest.main()
