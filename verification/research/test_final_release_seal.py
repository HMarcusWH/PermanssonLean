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
import archive_integrity as integrity

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
            "tex_sha256": digest((self.draft / "Permansson_Mathematical_Closure.tex").read_bytes()),
            "pdf_page_count": 1,
            "source_tree_files": {
                "research_papers/mathematical_closure/" + path:
                digest(("FAKE_SOURCE_" + path).encode())
                for path in integrity.SOURCE_FILES
            },
        }
        (self.draft / "manifest.lock.json").write_text(
            json.dumps(self.manifest))
        (self.draft / "latex_build.log").write_bytes(b"FAKE_TEX_LOG")
        self.manifest["latex_log_sha256"] = digest(b"FAKE_TEX_LOG")
        (self.draft / "manifest.lock.json").write_text(json.dumps(self.manifest))
        source_ci = {"status": "MISSING_POST_MERGE_SOURCE_AND_REVIEWS",
                     "ci_receipts": [], "independent_reviews": []}
        (self.draft / "source_ci_receipts.lock.json").write_text(json.dumps(source_ci))
        archive_path = self.draft / "Permansson_Mathematical_Closure_E2E.zip"
        with zipfile.ZipFile(archive_path, "w") as z:
            for path in integrity.SOURCE_FILES:
                z.writestr("manuscript/" + path,
                           ("FAKE_SOURCE_" + path).encode())
            for name in integrity.GENERATED:
                z.write(self.draft / name, name)
        (self.draft / "SHA256SUMS.txt").write_text("".join(
            digest((self.draft / name).read_bytes()) + "  " + name + "\n"
            for name in integrity.SUMMED))
        self.external_bundle = self.draft / "unavailable.zip"
        self.external_bundle.write_bytes(b"MOCK_EXTERNAL_UNREVIEWED_PROOF_BUNDLE")
        self.receipts = {
            "evidence_bundle_sha256": digest(self.external_bundle.read_bytes())
        }
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
            result = seal.seal(self.draft, self.approved, self.receipts,
                               self.external_bundle, self.output)
        self.assertEqual(result["status"], "APPROVED_SOURCE_BOUND")
        self.assertEqual((self.draft/"manifest.lock.json").read_bytes(), before)
        with zipfile.ZipFile(self.output/"Permansson_Mathematical_Closure_APPROVED.zip") as z:
            self.assertEqual(z.read("Permansson_Mathematical_Closure.pdf"), self.pdf)
            self.assertEqual(json.loads(z.read("original_draft_manifest.lock.json")),
                             self.manifest)
            self.assertEqual(z.read("detached_proof_mutation_bundle.zip"),
                             self.external_bundle.read_bytes())
            self.assertEqual(json.loads(z.read("source_acceptance_receipts.json")),
                             self.receipts)
            self.assertEqual(len([n for n in z.namelist()
                                  if n.startswith("manuscript/")]), 13)

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

    def test_connected_mock_preseal_postseal_replay_does_not_authorize(self):
        """Run actual ZIP/manifest/checksum/replay code end to end.

        The only substituted boundary is the external acceptance gate.
        These fixture bytes and their output are not GitHub or scholarly
        evidence, even when the candidate archive replays successfully.
        """
        import postseal_replay as replay
        from final_closure_full_contract import ORIGINAL_CLAIMS

        claims = sorted(ORIGINAL_CLAIMS)
        approved = dict(self.approved, claims=claims,
                        approved_manuscript_claims=claims)
        mock_external_review = {
            "source": M, "frozen_head": H,
            "status": "POSTMERGE_PRESEAL_READY",
            "accepted_case_count": 45, "accepted_claim_count": 11,
            "receipt_contract": "ALL_45_HISTORICAL_AND_ALL_11_COMPLETE",
            "effective_cases": {
                f"C-{index:02d}": "VERIFIED_SELECTED_SCOPE"
                for index in range(1, 46)},
            "effective_claims": claims,
        }
        # Explicit synthetic owner inputs; the external acceptance is mocked.
        owner_dir = Path(self.tmp.name) / "mock-original-owners"
        owner_dir.mkdir()
        for i in range(1, 77):
            (owner_dir / (str(i) + ".zip")).write_bytes(b"PK_fake_unreviewed")
        reproduction_zip = Path(self.tmp.name) / "mock-reproduction.zip"
        reproduction_zip.write_bytes(b"PK_fake_reproduction")
        extra_contract = Path(self.tmp.name) / "extra_contract.json"
        extra_contract.write_text("{}")
        workflow_blobs = Path(self.tmp.name) / "workflow_blobs.json"
        workflow_blobs.write_text("{}")
        reproduction = {"zip_file": reproduction_zip, "identities": {"synthetic": True}}
        v31 = {"additional_contract": extra_contract,
               "workflow_blob_candidates": workflow_blobs,
               "additional_zips": owner_dir}
        with mock.patch.object(
                seal.draft_verifier, "verify",
                return_value={"integrity": "TEST_FIXTURE_ONLY"}):
            with mock.patch.object(
                    seal, "strict_acceptance",
                    return_value=mock_external_review):
                result = seal.seal(
                    self.draft, approved, self.receipts,
                    self.external_bundle, self.output, full=True,
                    reproduction_attachment=reproduction, v31_attachment=v31)

        self.assertEqual(result["status"], "CANDIDATE_SEAL_BUILT")
        archive = self.output / "Permansson_Mathematical_Closure_CANDIDATE.zip"
        sidecar = self.output / "SHA256SUMS.txt"
        target = Path(self.tmp.name) / "detached" / "replay.json"
        receipt = replay.replay(archive, sidecar, target)
        self.assertEqual(
            receipt["status"], "CANDIDATE_ARCHIVE_REPLAYED_UNREVIEWED")
        self.assertEqual(receipt["source_commit_sha"], M)
        self.assertTrue(receipt["complete_original_members_verified"])
        self.assertEqual(json.loads(target.read_bytes()), receipt)
        for key in ("authenticated_ci_artifact", "independent_review",
                    "full_release_approved"):
            self.assertFalse(receipt[key], key)

        # The exact sidecar is mandatory: altered bytes must fail
        # independently of the simulated upstream review predicate.
        sidecar.write_text("0" * 64 + "  forged.zip\n")
        with self.assertRaises(seal.SealError):
            replay.replay(
                archive, sidecar,
                Path(self.tmp.name) / "tampered" / "replay.json")

    def test_partial_additional_evidence_inputs_fail_before_seal(self):
        approved = Path(self.tmp.name) / "approved.json"
        receipts = Path(self.tmp.name) / "receipts.json"
        approved.write_text(json.dumps(self.approved))
        receipts.write_text(json.dumps(self.receipts))
        args = [
            "--draft-dir", str(self.draft),
            "--approved-claim-manifest", str(approved),
            "--source-receipts", str(receipts),
            "--bundle", str(self.external_bundle),
            "--out", str(self.output),
        ]
        fields = ("--additional-contract", "--additional-zips",
                  "--workflow-blob-candidates")
        for flags in ((fields[0],), fields[:2], (fields[2],)):
            with self.subTest(flags=flags), mock.patch.object(
                    seal, "seal") as actual_seal:
                test_args = list(args)
                for flag in flags:
                    test_args.extend((flag, str(self.draft)))
                self.assertEqual(seal.main(test_args), 2)
                actual_seal.assert_not_called()
                self.assertFalse(self.output.exists())

    def test_full_seal_uses_preseal_not_the_circular_full_gate(self):
        from final_closure_full_contract import ORIGINAL_CLAIMS
        approved = dict(self.approved, claims=sorted(ORIGINAL_CLAIMS),
                        approved_manuscript_claims=sorted(ORIGINAL_CLAIMS))
        scopes = []
        def blocked(receipts, scope, manifest, bundle_path=None):
            scopes.append(scope)
            raise seal.SealError("no real independent preseal authorization")
        with mock.patch.object(seal.draft_verifier, "verify",
                               return_value={"integrity": "PASS"}), \
             mock.patch.object(seal, "strict_acceptance", side_effect=blocked):
            with self.assertRaises(seal.SealError):
                seal.seal(self.draft, approved, self.receipts,
                          self.external_bundle, self.output, full=True)
        self.assertEqual(scopes, ["postmerge-preseal-strict"])
        self.assertFalse(self.output.exists())

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


    def test_modified_approved_claim_member_rejects_even_with_new_zip_crc(self):
        """Reproduce the formerly accepted claim-member mutation."""
        with mock.patch.object(seal.draft_verifier, "verify", return_value={
                    "integrity": "TEST_ONLY"}), \
             mock.patch.object(seal, "strict_acceptance", return_value={
                    "source": M, "frozen_head": H,
                    "accepted_case_count": 1, "accepted_claim_count": 1}):
            seal.seal(self.draft, self.approved, self.receipts,
                      self.external_bundle, self.output)
        archive = self.output / "Permansson_Mathematical_Closure_APPROVED.zip"
        with zipfile.ZipFile(archive) as source:
            seal_manifest = json.loads(source.read("approved_seal.json"))
            members = {name: source.read(name) for name in source.namelist()}
        wrong_claims = json.loads(members["approved_claims_manifest.json"])
        wrong_claims["claims"] = ["MUTATED_CLAIM"]
        members["approved_claims_manifest.json"] = json.dumps(wrong_claims).encode()
        replacement = self.output / "rewritten.zip"
        with zipfile.ZipFile(replacement, "w", compression=zipfile.ZIP_DEFLATED) as zipped:
            for name, raw in sorted(members.items()):
                zipped.writestr(name, raw)
        with self.assertRaises(seal.SealError):
            seal.verify_approved_archive(replacement, seal_manifest)

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
