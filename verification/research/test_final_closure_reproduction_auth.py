"""Mock GitHub API + original ZIP adversaries; never real release evidence."""
import io
import json
from pathlib import Path
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


def artifact_fixture():
    report={
        "format":"Permansson.TwoCleanSourceRebuilds.v1",
        "status":"REPRODUCIBLE_DRAFT_ONLY",
        "source_commit_sha":M,
        "source_tree_sha":"b"*40,
        "independent_source_roots":2,
        "git_clone_mode":"local_no_hardlinks_no_checkout",
        "engine":"pdflatex","rendered_pages":True,
        "pdf_sha256":auth.sha(PDF),
        "archive_sha256":auth.sha(ARCHIVE),
        "manifest_sha256":None,
        "two_complete_archive_audits":True,
        "byte_comparison":{
            "status":"REPRODUCIBLE_DRAFT_ONLY",
            "source_commit_sha":M,
            "pdf_sha256":auth.sha(PDF),
            "zip_sha256":auth.sha(ARCHIVE),
            "page_count":1},
        "authenticated_ci_artifact":False,
        "scientific_release_approved":False,
    }
    manifest={
        "source_commit_sha":M,"status":"DRAFT_NOT_ACCEPTED",
        "pdf_sha256":auth.sha(PDF),"pdf_page_count":1,
    }
    mb=json.dumps(manifest).encode()
    report["manifest_sha256"]=auth.sha(mb)
    identity={
        "format":"Permansson.CICleanRebuildCandidate.v1",
        "status":"EXECUTED_DRAFT_ONLY_NO_SCHOLARLY_REVIEW",
        "source_head":M,"github_repository":"HMarcusWH/PermanssonLean",
        "github_job":"clean-paper-rebuild",
        "github_run_id":101,"github_run_attempt":1,
        "pdf_sha256":auth.sha(PDF),
        "archive_sha256":auth.sha(ARCHIVE),
        "authenticated_ci_artifact":False,
    }
    items={
        "reproduction_receipt.json":json.dumps(report).encode(),
        "ci_execution_identity.json":json.dumps(identity).encode(),
    }
    same={
        "Permansson_Mathematical_Closure.pdf":PDF,
        "Permansson_Mathematical_Closure_E2E.zip":ARCHIVE,
        "manifest.lock.json":mb,
        "Permansson_Mathematical_Closure.tex":b"fake tex",
        "latex_build.log":b"fake build log",
        "SHA256SUMS.txt":b"fake sidecar",
        "source_ci_receipts.lock.json":b"false approval flags absent",
        "pages/page-1.png":PAGE,
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

    def attest(self):
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
                M,auth.sha(PDF),IDS,self.path)

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
                payload=auth.inspect_zip(make_zip(contents))
                with self.assertRaises(auth.ReproductionAuthenticationError):
                    auth.validate_clean_root_bytes(
                        payload,merged=M,expected_pdf=auth.sha(PDF))
