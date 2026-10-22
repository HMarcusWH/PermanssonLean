"""Byte integrity tests; mocked approvals are NEVER actual release evidence."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock
import zipfile

ROOT = Path(__file__).resolve().parents[2]
RELEASE = ROOT / "release/mathematical-closure-1"
if str(RELEASE) not in sys.path:
    sys.path.insert(0, str(RELEASE))
import reproduce
import seal_approved as seal

H = "a" * 40
M = "b" * 40
digest = lambda x: hashlib.sha256(x).hexdigest()


class ApprovedSealByteTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="perm-seal-test-")
        self.addCleanup(self.tmp.cleanup)
        base = Path(self.tmp.name)
        self.draft = base / "draft"
        self.draft.mkdir()
        self.output = base / "approved"
        self.pdf = b"%PDF-1.4\nFAKE TEST BYTES ONLY\n"
        (self.draft / "Permansson_Mathematical_Closure.pdf").write_bytes(self.pdf)
        (self.draft / "Permansson_Mathematical_Closure.tex").write_text(
            "% Mock TeX without real paper/reviewer\n")
        (self.draft / "pages").mkdir()
        (self.draft / "pages" / "page-1.png").write_bytes(b"MOCK PNG")
        self.pdfsha = digest(self.pdf)
        self.pages = {"page-1.png": digest(b"MOCK PNG")}
        self.manifest = {
            "format": "Permansson.MathClosure.BuildReceipt.v1",
            "status": "DRAFT_NOT_ACCEPTED", "mode": "DRAFT",
            "source_commit_sha": M, "pdf_sha256": self.pdfsha,
            "pdf_page_count": 1, "source_tree_files": {},
        }
        (self.draft / "manifest.lock.json").write_text(
            json.dumps(self.manifest))
        self.approved = {
            "status": "APPROVED_SOURCE_BOUND", "source_commit_sha": M,
            "pdf_sha256": self.pdfsha, "pdf_pages": self.pages,
            "claims": ["Q1"], "scientific_limitations": ["no empirical GR/PR"],
            "empirical_identification_status": "NOT_ESTABLISHED",
        }

    def test_changed_pdf_or_unrendered_page_never_seals(self):
        approval = dict(self.approved, pdf_sha256="0"*64)
        with self.assertRaises(seal.SealError):
            seal.prepare_approved_manifest(self.draft, approval)
        (self.draft/"pages"/"page-1.png").unlink()
        with self.assertRaises(seal.SealError):
            seal.prepare_approved_manifest(self.draft, self.approved)

    def test_mocked_seal_preserves_original_draft_and_exact_bytes(self):
        before = (self.draft/"manifest.lock.json").read_bytes()
        with mock.patch.object(seal.draft_verifier, "verify", return_value={
                    "integrity": "PASS", "accepted": False}), \
             mock.patch.object(seal, "strict_acceptance", return_value={
                    "source": M, "frozen_head": H,
                    "accepted_case_count": 1, "accepted_claim_count": 1}):
            result = seal.seal(self.draft, self.approved, {},
                               self.draft/"unavailable.zip", self.output)
        self.assertEqual(result["status"], "APPROVED_SOURCE_BOUND")
        self.assertEqual((self.draft/"manifest.lock.json").read_bytes(), before)
        with zipfile.ZipFile(self.output/"Permansson_Mathematical_Closure_APPROVED.zip") as z:
            self.assertEqual(z.read("Permansson_Mathematical_Closure.pdf"), self.pdf)
            self.assertEqual(json.loads(z.read("original_draft_manifest.lock.json")),
                             self.manifest)

    def test_full_seal_cannot_promote_partial_scope(self):
        from final_closure_full_contract import ORIGINAL_CLAIMS
        approved = dict(self.approved,
                        claims=sorted(ORIGINAL_CLAIMS),
                        approved_manuscript_claims=sorted(ORIGINAL_CLAIMS))
        with mock.patch.object(seal.draft_verifier, "verify",
                               return_value={"integrity": "PASS"}), \
             mock.patch.object(seal, "strict_acceptance",
                               return_value={
                                   "source": M, "frozen_head": H,
                                   "status": "FULL_MATHEMATICAL_CLOSURE_RELEASE_READY",
                                   "accepted_case_count": 44,
                                   "accepted_claim_count": 11}):
            with self.assertRaises(seal.SealError):
                seal.seal(self.draft, approved, {},
                          self.draft/"fake_bundle.zip", self.output, full=True)

    def test_full_seal_mocked_success_still_requires_exact_claim_set(self):
        with mock.patch.object(seal.draft_verifier, "verify",
                               return_value={"integrity": "PASS"}), \
             mock.patch.object(seal, "strict_acceptance",
                               return_value={
                                   "source": M, "frozen_head": H,
                                   "status": "FULL_MATHEMATICAL_CLOSURE_RELEASE_READY",
                                   "accepted_case_count": 45,
                                   "accepted_claim_count": 11}):
            with self.assertRaises(seal.SealError):
                seal.seal(self.draft, self.approved, {},
                          self.draft/"fake_bundle.zip", self.output, full=True)

    def test_reproducibility_reports_different_bytes_instead_of_relabeling(self):
        first, second = self.draft, Path(self.tmp.name)/"second"
        import shutil
        shutil.copytree(first, second)
        for name in reproduce.FILES:
            payload = (json.dumps(self.manifest).encode()
                       if name == "manifest.lock.json" else b"identical")
            (first/name).write_bytes(payload)
            (second/name).write_bytes(payload)
        data = reproduce.compare_artifacts(first, second)
        self.assertEqual(data["status"], "REPRODUCIBLE_DRAFT_ONLY")
        (second/"Permansson_Mathematical_Closure.pdf").write_bytes(b"different")
        with self.assertRaises(reproduce.ReproducibilityError):
            reproduce.compare_artifacts(first, second)

    def test_approved_archive_cannot_contain_extra_members(self):
        archive = Path(self.tmp.name)/"bad.zip"
        manifest = {"pdf_sha256": self.pdfsha, "pdf_pages": self.pages}
        with zipfile.ZipFile(archive, "w") as z:
            z.writestr("approved_seal.json", json.dumps(manifest))
            z.writestr("unexpected", b"malicious")
        with self.assertRaises(seal.SealError):
            seal.verify_approved_archive(archive, manifest)


if __name__ == "__main__":
    unittest.main()
