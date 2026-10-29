"""No incomplete draft may masquerade as a mathematical release."""
import copy,io,json,sys,tempfile,unittest,zipfile
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock
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


class FullArchiveDigestBindingTests(unittest.TestCase):
    """Real ZIP bytes and structural checks; external authority is SYNTHETIC."""

    def setUp(self):
        # Reuse the existing byte-complete synthetic draft without inheriting
        # its test methods. No compiler, reviewer or GitHub approval is created.
        from test_final_release_seal import ApprovedSealByteTests
        from final_closure_full_contract import ORIGINAL_CLAIMS
        from pr113_owner_partition_v3 import FORMAT as OWNER_FORMAT
        import seal_approved as seal
        ApprovedSealByteTests.setUp(self)
        self.sealer = seal
        self.base = Path(self.tmp.name)
        claims = sorted(ORIGINAL_CLAIMS)
        self.approved = dict(self.approved, claims=claims,
                             approved_manuscript_claims=claims)
        self.preseal = {
            "source": "b" * 40, "frozen_head": "a" * 40,
            "status": "POSTMERGE_PRESEAL_READY",
            "accepted_case_count": 45, "accepted_claim_count": 11,
            "receipt_contract": "ALL_45_HISTORICAL_AND_ALL_11_COMPLETE",
            "effective_cases": {f"C-{i:02d}": "VERIFIED_SELECTED_SCOPE"
                                for i in range(1, 46)},
            "effective_claims": claims,
        }
        self.owner_dir = self.base / "synthetic-owner-artifacts"
        self.owner_dir.mkdir()
        for artifact in (101, 102, 103):
            (self.owner_dir / (str(artifact) + ".zip")).write_bytes(
                b"PK_SYNTHETIC_UNREVIEWED_OWNER_INPUT")
        owner_groups = (
            (101, "original_positive", [f"C-{i:02d}" for i in range(1, 46)]),
            (102, "legacy_negative", [f"C-{i:02d}" for i in range(1, 21)]),
            (103, "claim_pair", claims),
        )
        registry = {
            "format": OWNER_FORMAT, "source_controls_accepted": False,
            "independent_security_review": False, "mathematical_approval": False,
            "producers": [{"artifact_id": artifact, "owners": [
                {"kind": kind, "owner_id": owner} for owner in owners]}
                for artifact, kind, owners in owner_groups],
        }
        self.contract = self.base / "synthetic-owner-contract.json"
        self.contract.write_text(json.dumps(registry), encoding="utf-8")
        self.workflow = self.base / "synthetic-workflow-blobs.json"
        self.workflow.write_text("{}", encoding="utf-8")
        self.reproduction = self.base / "synthetic-reproduction.zip"
        self.reproduction.write_bytes(b"PK_SYNTHETIC_UNREVIEWED_REPRODUCTION")
        self.reproduction_ids = self.base / "synthetic-reproduction-ids.json"
        self.reproduction_ids.write_text('{"synthetic": true}', encoding="utf-8")
        with mock.patch.object(seal.draft_verifier, "verify", return_value={
                "integrity": "SYNTHETIC_DRAFT_FIXTURE"}), mock.patch.object(
                seal, "strict_acceptance", return_value=self.preseal):
            seal.seal(self.draft, self.approved, self.receipts,
                      self.external_bundle, self.output, full=True,
                      reproduction_attachment={"zip_file": self.reproduction,
                                               "identities": {"synthetic": True}},
                      reproduction_ids_source=self.reproduction_ids,
                      v31_attachment={"additional_contract": self.contract,
                                      "additional_zips": self.owner_dir,
                                      "workflow_blob_candidates": self.workflow})
        self.archive = self.output / "Permansson_Mathematical_Closure_CANDIDATE.zip"

    def outcome(self):
        return {**self.preseal, "status": "FULL_MATHEMATICAL_CLOSURE_RELEASE_READY",
                "authenticated_archive_sha256": vr.sha(self.archive)}

    def invoke(self, archive, outcome):
        approved_file, receipts_file = self.base / "approved.json", self.base / "receipts.json"
        approved_file.write_text(json.dumps(self.approved), encoding="utf-8")
        receipts_file.write_text(json.dumps(self.receipts), encoding="utf-8")
        argv = ["--manifest", str(self.draft / "manifest.lock.json"),
                "--approved-seal", str(archive),
                "--source-receipts", str(receipts_file),
                "--approved-manifest", str(approved_file),
                "--bundle", str(self.external_bundle),
                "--additional-contract", str(self.contract),
                "--additional-zips", str(self.owner_dir),
                "--workflow-blob-candidates", str(self.workflow)]
        stdout, stderr = io.StringIO(), io.StringIO()
        # Only the independent external authentication boundary is synthetic;
        # the CLI and actual candidate-ZIP structural verifier remain real.
        with mock.patch("final_closure_verify.strict", return_value=outcome) as auth, \
                redirect_stdout(stdout), redirect_stderr(stderr):
            code = vr.main(argv)
        return code, stdout.getvalue(), stderr.getvalue(), auth.call_args.args[1]

    def test_full_release_rejects_different_rehashed_zip_with_same_reviewed_fields(self):
        with zipfile.ZipFile(self.archive) as source:
            members = {name: source.read(name) for name in source.namelist()}
        original = json.loads(members["approved_seal.json"])
        altered = copy.deepcopy(original)
        members["detached_proof_mutation_bundle.zip"] = b"SYNTHETIC_ALTERED_EVIDENCE"
        changed_receipts = json.loads(members["source_acceptance_receipts.json"])
        altered["evidence_bundle_sha256"] = vr.hashlib.sha256(
            members["detached_proof_mutation_bundle.zip"]).hexdigest()
        changed_receipts["evidence_bundle_sha256"] = altered["evidence_bundle_sha256"]
        members["source_acceptance_receipts.json"] = json.dumps(changed_receipts).encode()
        altered["source_receipts_sha256"] = vr.hashlib.sha256(
            members["source_acceptance_receipts.json"]).hexdigest()
        members["approved_seal.json"] = json.dumps(altered).encode()
        substitute = self.base / "synthetic-internally-consistent-substitute.zip"
        with zipfile.ZipFile(substitute, "w") as zipped:
            for name, raw in sorted(members.items()):
                entry = zipfile.ZipInfo(name, (1980, 1, 1, 0, 0, 0))
                entry.external_attr = 0o100644 << 16
                zipped.writestr(entry, raw)
        # Both genuinely pass the unchanged structural checker, and all fields
        # compared by the former CLI are identical. Only the whole ZIP differs.
        self.sealer.verify_approved_archive(self.archive, original)
        self.sealer.verify_approved_archive(substitute, altered)
        for key in ("source_commit_sha", "head_sha", "pdf_sha256", "pdf_pages", "claims"):
            self.assertEqual(original[key], altered[key], key)
        self.assertNotEqual(vr.sha(self.archive), vr.sha(substitute))
        self.assertEqual(self.invoke(self.archive, self.outcome())[0], 0)
        code, stdout, stderr, scope = self.invoke(substitute, self.outcome())
        self.assertEqual(code, 2, stdout + stderr)
        self.assertNotIn('"accepted": true', stdout)
        self.assertIn("authenticated postseal archive", stderr)
        self.assertEqual(scope, "full-release-strict")

    def test_full_release_rejects_missing_or_malformed_authenticated_zip_digest(self):
        for digest in (None, "", "not-a-sha256", "0" * 64):
            with self.subTest(digest=digest):
                outcome = self.outcome()
                if digest is None:
                    del outcome["authenticated_archive_sha256"]
                else:
                    outcome["authenticated_archive_sha256"] = digest
                code, stdout, stderr, scope = self.invoke(self.archive, outcome)
                self.assertEqual(code, 2, stdout + stderr)
                self.assertNotIn('"accepted": true', stdout)
                self.assertEqual(scope, "full-release-strict")

    def test_scoped_archive_retains_its_existing_contract_without_postseal_digest(self):
        output = self.base / "scoped-synthetic-archive"
        with mock.patch.object(self.sealer.draft_verifier, "verify", return_value={
                "integrity": "SYNTHETIC_DRAFT_FIXTURE"}), mock.patch.object(
                self.sealer, "strict_acceptance", return_value=self.preseal):
            self.sealer.seal(self.draft, self.approved, self.receipts,
                             self.external_bundle, output)
        archive = output / "Permansson_Mathematical_Closure_APPROVED.zip"
        outcome = {"source": self.preseal["source"],
                   "frozen_head": self.preseal["frozen_head"]}
        code, stdout, stderr, scope = self.invoke(archive, outcome)
        self.assertEqual(code, 0, stderr)
        self.assertEqual(scope, "scoped-release-strict")
        self.assertEqual(json.loads(stdout)["scope"], "SCOPED_ONLY")

if __name__=="__main__":unittest.main()
