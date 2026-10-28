"""Mock GitHub API + original ZIP adversaries; never real release evidence."""
import io
import json
from pathlib import Path
import stat
import tempfile
import unittest
from unittest import mock
import zipfile

import final_closure_reproduction_auth as auth

M="a"*40
PDF=b"%PDF-1.7\nSYNTHETIC TEST CONTENT\n"
ARCHIVE=b"synthetic-archive-not-real-research"
PAGE=b"png-mocked-page-bytes"
IDS={"run_id":101,"run_attempt":1,"job_id":102,"check_run_id":103,
     "artifact_id":104}


def artifact_fixture(pdf=PDF, archive=ARCHIVE, page=PAGE):
    report={
        "format":"Permansson.TwoCleanSourceRebuilds.v1",
        "status":"REPRODUCIBLE_DRAFT_ONLY",
        "source_commit_sha":M,
        "source_tree_sha":"b"*40,
        "independent_source_roots":2,
        "git_clone_mode":"local_no_hardlinks_no_checkout",
        "engine":"pdflatex","rendered_pages":True,
        "pdf_sha256":auth.sha(pdf),
        "archive_sha256":auth.sha(archive),
        "manifest_sha256":None,
        "two_complete_archive_audits":True,
        "byte_comparison":{
            "status":"REPRODUCIBLE_DRAFT_ONLY",
            "source_commit_sha":M,
            "pdf_sha256":auth.sha(pdf),
            "zip_sha256":auth.sha(archive),
            "page_count":1},
        "authenticated_ci_artifact":False,
        "scientific_release_approved":False,
    }
    manifest={
        "source_commit_sha":M,"status":"DRAFT_NOT_ACCEPTED",
        "pdf_sha256":auth.sha(pdf),"pdf_page_count":1,
    }
    mb=json.dumps(manifest).encode()
    report["manifest_sha256"]=auth.sha(mb)
    identity={
        "format":"Permansson.CICleanRebuildCandidate.v1",
        "status":"EXECUTED_DRAFT_ONLY_NO_SCHOLARLY_REVIEW",
        "source_head":M,"github_repository":"HMarcusWH/PermanssonLean",
        "github_job":"clean-paper-rebuild",
        "github_run_id":101,"github_run_attempt":1,
        "pdf_sha256":auth.sha(pdf),
        "archive_sha256":auth.sha(archive),
        "authenticated_ci_artifact":False,
    }
    items={
        "reproduction_receipt.json":json.dumps(report).encode(),
        "ci_execution_identity.json":json.dumps(identity).encode(),
    }
    same={
        "Permansson_Mathematical_Closure.pdf":pdf,
        "Permansson_Mathematical_Closure_E2E.zip":archive,
        "manifest.lock.json":mb,
        "Permansson_Mathematical_Closure.tex":b"fake tex",
        "latex_build.log":b"fake build log",
        "SHA256SUMS.txt":b"fake sidecar",
        "source_ci_receipts.lock.json":b"false approval flags absent",
        "pages/page-1.png":page,
    }
    for side in ("first","second"):
        for name,body in same.items():
            items[side+"/"+name]=body
    return items


def make_zip(members):
    data=io.BytesIO()
    with zipfile.ZipFile(data,"w") as z:
        for name,body in sorted(members.items()):
            z.writestr(name,body)
    return data.getvalue()


class MergedCleanEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix="perm-clean-gh-")
        self.addCleanup(self.tmp.cleanup)
        self.path=Path(self.tmp.name)/"draft.zip"
        self.contents=artifact_fixture()
        self.build()
        self.run={
            "id":101,"head_sha":M,"head_branch":"main",
            "run_attempt":1,"status":"completed","conclusion":"success",
            "event":"workflow_dispatch","path":auth.WORKFLOW,
        }
        self.job={
            "id":102,"name":"clean-paper-rebuild","run_id":101,
            "run_attempt":1,"head_sha":M,"status":"completed",
            "conclusion":"success",
            "check_run_url":
             "https://api.github.com/repos/HMarcusWH/PermanssonLean/check-runs/103",
        }
        self.check={
            "id":103,"head_sha":M,"name":"clean-paper-rebuild",
            "status":"completed","conclusion":"success",
            "app":{"slug":"github-actions"},
        }
        self.artifact={
            "id":104,"name":auth.ARTIFACT,"expired":False,
            "digest":"sha256:"+auth.sha(self.path.read_bytes()),
            "workflow_run":{"id":101,"head_sha":M},
        }

    def build(self):
        self.path.write_bytes(make_zip(self.contents))

    def attest(self, expected_pdf=PDF):
        api={
            "/actions/runs/101":self.run,
            "/check-runs/103":self.check,
            "/actions/artifacts/104":self.artifact,
        }
        with mock.patch.object(auth, "live",
                               side_effect=lambda path:api[path]), \
             mock.patch.object(auth, "paginate",
                               return_value=[self.job]):
            return auth.authenticate_merged_reproduction(
                M,auth.sha(expected_pdf),IDS,self.path)

    def test_exact_success_is_authenticated_only_as_clean_build(self):
        result=self.attest()
        self.assertEqual(result["status"],"TWO_CLEAN_SOURCE_BUILDS")
        self.assertTrue(result["authenticated_ci_artifact"])
        self.assertFalse(result["scholarly_review_approved"])
        self.assertFalse(result["mathematical_release_approved"])
        self.assertEqual(result["rendered_page_count"],1)

    def test_wrong_head_run_attempt_job_and_source_rejected(self):
        mutations=[
            lambda:self.run.update(head_sha="f"*40),
            lambda:self.run.update(run_attempt=2),
            lambda:self.job.update(conclusion="failure"),
            lambda:self.check.update(conclusion="failure"),
            lambda:self.artifact.update(digest="sha256:"+"f"*64),
            lambda:self.run.update(head_branch="research/final-mathematical-closure"),
        ]
        for index,mutation in enumerate(mutations):
            with self.subTest(index=index):
                self.setUp()
                mutation()
                with self.assertRaises(auth.ReproductionAuthenticationError):
                    self.attest()

    def test_changed_pdf_missing_page_or_forged_receipt_rejected(self):
        attacks=[
            lambda c:c.update({"second/Permansson_Mathematical_Closure.pdf":b"altered"}),
            lambda c:c.pop("second/pages/page-1.png"),
            lambda c:c.update({"first/pages/page-1.png":b"altered"}),
            lambda c:c.update({"reproduction_receipt.json":
                                json.dumps({"status":"TWO_CLEAN_SOURCE_BUILDS",
                                            "authenticated_ci_artifact":True}).encode()}),
        ]
        for idx,attack in enumerate(attacks):
            with self.subTest(idx=idx):
                contents=artifact_fixture()
                attack(contents)
                payload=auth.inspect_reproduction_zip(make_zip(contents))
                with self.assertRaises(auth.ReproductionAuthenticationError):
                    auth.validate_clean_root_bytes(
                        payload,merged=M,expected_pdf=auth.sha(PDF))

    def test_large_pdf_nested_zip_and_work_pdf_preserve_authenticated_bytes(self):
        # Real stored ZIP bytes and literal >5MiB PDF-shaped test data; live
        # GitHub identities and scholarly authority remain explicitly synthetic.
        from final_closure_producer_bytes import inspect_zip, ProducerBytesError
        pdf = PDF + b"% synthetic PDF test padding\n" * 200_000
        nested = make_zip({"synthetic-only.bin": b"x" * (5 * 1024 * 1024)})
        self.assertGreater(len(pdf), 5 * 1024 * 1024)
        self.assertGreater(len(nested), 5 * 1024 * 1024)
        self.contents = artifact_fixture(pdf=pdf, archive=nested)
        self.contents["first/_texwork/main.pdf"] = pdf
        self.contents["second/_texwork/main.pdf"] = pdf
        self.contents["first/latex_build.raw.log"] = b"retained original compiler diagnostics"
        self.contents["first/_texwork/main.aux"] = b"retained original TeX auxiliary"
        self.build()
        raw = self.path.read_bytes()
        self.assertLess(len(raw), auth.MAX_ZIP_BYTES)
        with self.assertRaises(ProducerBytesError):
            inspect_zip(raw)
        self.artifact["digest"] = "sha256:" + auth.sha(raw)
        result = self.attest(expected_pdf=pdf)
        self.assertEqual(result["status"], "TWO_CLEAN_SOURCE_BUILDS")
        self.assertEqual(result["artifact_sha256"], auth.sha(raw))
        self.assertFalse(result["mathematical_release_approved"])

    def test_large_allowance_is_restricted_to_exact_binary_paths(self):
        large = b"x" * (4 * 1024 * 1024 + 1)
        for name in ("first/other.pdf", "first/_texwork/not-main.pdf",
                     "first/pages/other.png", "other/Permansson_Mathematical_Closure.pdf",
                     "reproduction_receipt.json"):
            with self.subTest(name=name), self.assertRaises(auth.ReproductionAuthenticationError):
                auth.inspect_reproduction_zip(make_zip({name: large}))
        # Known safe small auxiliary paths retain the original generic policy.
        tiny = {"first/_texwork/engine-specific.aux": b"small retained metadata"}
        self.assertEqual(auth.inspect_reproduction_zip(make_zip(tiny)), tiny)

    def test_typed_and_total_header_budgets_reject_before_decompression(self):
        self.assertEqual(auth.MAX_ZIP_BYTES, 64 * 1024 * 1024)
        self.assertEqual(auth.MAX_EXPANDED_BYTES, 512 * 1024 * 1024)
        self.assertEqual(auth.MAX_METADATA_BYTES, 4 * 1024 * 1024)
        self.assertEqual(auth.MAX_PDF_OR_PAGE_BYTES, 32 * 1024 * 1024)
        self.assertEqual(auth.MAX_DRAFT_ZIP_BYTES, 48 * 1024 * 1024)
        original = zipfile.ZipFile.infolist
        for name, budget in (("first/Permansson_Mathematical_Closure.pdf", auth.MAX_PDF_OR_PAGE_BYTES),
                             ("first/pages/page-1.png", auth.MAX_PDF_OR_PAGE_BYTES),
                             ("second/Permansson_Mathematical_Closure_E2E.zip", auth.MAX_DRAFT_ZIP_BYTES),
                             ("ci_execution_identity.json", auth.MAX_METADATA_BYTES)):
            raw = make_zip({name: b"x"})
            def declared_too_big(archive):
                rows = original(archive)
                rows[0].file_size = budget + 1
                return rows
            with self.subTest(name=name), mock.patch.object(zipfile.ZipFile, "infolist", declared_too_big), \
                    mock.patch.object(zipfile.ZipFile, "open") as reader:
                with self.assertRaises(auth.ReproductionAuthenticationError):
                    auth.inspect_reproduction_zip(raw)
                reader.assert_not_called()
        raw = make_zip({"first/pages/page-%d.png" % i: b"x" for i in range(17)})
        def declared_total(archive):
            rows = original(archive)
            for row in rows:
                row.file_size = auth.MAX_PDF_OR_PAGE_BYTES
            return rows
        with mock.patch.object(zipfile.ZipFile, "infolist", declared_total), \
                mock.patch.object(zipfile.ZipFile, "open") as reader:
            with self.assertRaises(auth.ReproductionAuthenticationError):
                auth.inspect_reproduction_zip(raw)
            reader.assert_not_called()

    def test_path_modes_aliases_counts_and_metadata_budget_fail_closed(self):
        for bad in ("../bad", "/bad", "first//bad", "first/pages/"):
            with self.subTest(path=bad), self.assertRaises(auth.ReproductionAuthenticationError):
                auth.inspect_reproduction_zip(make_zip({bad: b"x"}))
        # ZipInfo on Windows normalizes a constructor backslash; mutate both
        # original filename headers so this remains a real adversarial ZIP.
        backslash = make_zip({"first/bad": b"x"}).replace(b"first/bad", b"first\\bad")
        with self.assertRaises(auth.ReproductionAuthenticationError):
            auth.inspect_reproduction_zip(backslash)
        for pair in (("first/file", "FIRST/FILE"), ("first/pages", "first/pages/page-1.png")):
            with self.subTest(pair=pair), self.assertRaises(auth.ReproductionAuthenticationError):
                auth.inspect_reproduction_zip(make_zip({name: b"x" for name in pair}))
        for mode in (stat.S_IFLNK, stat.S_IFDIR, stat.S_IFIFO):
            payload = io.BytesIO()
            with zipfile.ZipFile(payload, "w") as archive:
                entry = zipfile.ZipInfo("first/unsafe")
                entry.create_system = 3
                entry.external_attr = (mode | 0o600) << 16
                archive.writestr(entry, b"x")
            with self.subTest(mode=mode), self.assertRaises(auth.ReproductionAuthenticationError):
                auth.inspect_reproduction_zip(payload.getvalue())
        with self.assertRaises(auth.ReproductionAuthenticationError):
            auth.inspect_reproduction_zip(make_zip({"small-%d" % i: b"x" for i in range(513)}))

    def test_compressed_input_budget_is_checked_before_opening_file(self):
        with mock.patch.object(auth, "MAX_ZIP_BYTES", self.path.stat().st_size - 1), \
                mock.patch.object(Path, "open") as reader:
            with self.assertRaisesRegex(auth.ReproductionAuthenticationError, "compressed byte budget"):
                self.attest()
            reader.assert_not_called()

    def test_noncanonical_or_wrong_transport_digest_still_rejected(self):
        for digest in (None, "sha256:not-a-digest", "sha256:" + "f" * 64):
            with self.subTest(digest=digest):
                self.artifact["digest"] = digest
                with self.assertRaises(auth.ReproductionAuthenticationError):
                    self.attest()
