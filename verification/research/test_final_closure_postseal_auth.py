"""Postseal GitHub job/ZIP authentication adversaries; mock-only not approval."""
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock
import zipfile

import final_closure_postseal_auth as auth

M="a"*40
PDF="b"*64
IDS={"run_id":101,"run_attempt":1,"job_id":102,
     "check_run_id":103,"artifact_id":104}

def artifact_bytes():
    out=io.BytesIO()
    with zipfile.ZipFile(out,"w") as z:
        z.writestr("candidate/Permansson_Mathematical_Closure_CANDIDATE.zip",
                   b"mock candidate")
        z.writestr("candidate/SHA256SUMS.txt",b"mock sidecar")
        z.writestr("postseal_replay_receipt.json",json.dumps({
            "format":"Permansson.MathClosure.PostsealReplayCandidate.v1",
            "status":"CANDIDATE_ARCHIVE_REPLAYED_UNREVIEWED",
            "source_commit_sha":M,"head_sha":"c"*40,
            "pdf_sha256":PDF,
            "archive_sha256":auth.sha(b"mock candidate"),
            "complete_original_members_verified":True,
            "authenticated_ci_artifact":False,
            "independent_review":False,"full_release_approved":False,
        }))
    return out.getvalue()

class PostsealAuthTests(unittest.TestCase):
    def setUp(self):
        tmp=tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.file=Path(tmp.name)/"original.zip"
        self.file.write_bytes(artifact_bytes())
        self.run={"id":101,"head_sha":M,"head_branch":"main",
                  "event":"workflow_dispatch","run_attempt":1,
                  "status":"completed","conclusion":"success",
                  "path":auth.WORKFLOW}
        self.job={"id":102,"run_id":101,"head_sha":M,"run_attempt":1,
                  "name":auth.JOB,"status":"completed","conclusion":"success",
                  "check_run_url":"https://api.github.com/repos/HMarcusWH/PermanssonLean/check-runs/103"}
        self.check={"id":103,"head_sha":M,"name":auth.JOB,
                    "status":"completed","conclusion":"success",
                    "app":{"slug":"github-actions"}}
        self.artifact={"id":104,"name":auth.ARTIFACT,"expired":False,
                       "digest":"sha256:"+auth.sha(self.file.read_bytes()),
                       "workflow_run":{"id":101,"head_sha":M}}

    def invoke(self):
        api={"/actions/runs/101":self.run,"/check-runs/103":self.check,
             "/actions/artifacts/104":self.artifact}
        with mock.patch.object(auth,"live",side_effect=lambda path:api[path]), \
             mock.patch.object(auth,"paginate",return_value=[self.job]), \
             mock.patch.object(auth,"validate_postseal_payload",
                               return_value={"archive_sha256":auth.sha(b"mock candidate")}):
            return auth.authenticate_postseal(M,PDF,IDS,self.file)

    def test_reproduced_archive_receipt_still_has_no_scholarly_authority(self):
        observed=self.invoke()
        self.assertEqual(observed["status"],"COMPLETE_ARCHIVE_REPLAY")
        self.assertTrue(observed["authenticated_ci_artifact"])
        self.assertFalse(observed["independent_scholarly_approval"])
        self.assertFalse(observed["mathematical_release_approved"])

    def test_borrowed_or_unreviewed_workflow_does_not_promote(self):
        for name,field,value in (
            ("branch","run","wrong"),
            ("head","run","wrong"),
            ("event","run","push"),
            ("attempt","run",2),
            ("job","job","failure"),
            ("check","check","failure"),
            ("digest","artifact","sha256:"+"f"*64),
        ):
            with self.subTest(fault=name):
                self.setUp()
                if name=="branch":self.run["head_branch"]=value
                elif name=="head":self.run["head_sha"]=value
                elif name=="event":self.run["event"]=value
                elif name=="attempt":self.run["run_attempt"]=value
                elif name=="job":self.job["conclusion"]=value
                elif name=="check":self.check["conclusion"]=value
                elif name=="digest":self.artifact["digest"]=value
                with self.assertRaises(auth.PostsealAuthenticationError):
                    self.invoke()

    def test_local_replay_flags_cannot_substitute_for_nested_bytes(self):
        entries={
            "postseal_replay_receipt.json":json.dumps({
                "format":"Permansson.MathClosure.PostsealReplayCandidate.v1",
                "status":"FULL_MATHEMATICAL_CLOSURE_RELEASE_READY",
                "source_commit_sha":M,"pdf_sha256":PDF,
                "authenticated_ci_artifact":True}).encode(),
            "candidate/Permansson_Mathematical_Closure_CANDIDATE.zip":
                b"fake archive",
            "candidate/SHA256SUMS.txt":b"fake",
        }
        with self.assertRaises(auth.PostsealAuthenticationError):
            auth.validate_postseal_payload(entries,merged=M,expected_pdf=PDF)
        entries.pop("candidate/SHA256SUMS.txt")
        with self.assertRaises(auth.PostsealAuthenticationError):
            auth.validate_postseal_payload(entries,merged=M,expected_pdf=PDF)
