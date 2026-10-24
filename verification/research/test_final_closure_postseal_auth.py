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
     "check_run_id":103,"artifact_id":104,
     "upstream_run_id":201,"upstream_run_attempt":2,"upstream_job_id":202,
     "upstream_check_run_id":203,"upstream_artifact_id":204}
UPSTREAM_DIGEST="e"*64

def upstream_metadata():
    return {"id":204,"name":auth.UPSTREAM_ARTIFACT,"expired":False,
            "digest":"sha256:"+UPSTREAM_DIGEST,
            "created_at":"2026-10-24T08:05:00Z",
            "workflow_run":{"id":201,"head_sha":M}}

def artifact_bytes(metadata=None):
    out=io.BytesIO()
    with zipfile.ZipFile(out,"w") as z:
        z.writestr(auth.UPSTREAM_METADATA,json.dumps(
            upstream_metadata() if metadata is None else metadata))
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
                  "path":auth.WORKFLOW,
                  "run_started_at":"2026-10-24T09:00:00Z"}
        self.job={"id":102,"run_id":101,"head_sha":M,"run_attempt":1,
                  "name":auth.JOB,"status":"completed","conclusion":"success",
                  "started_at":"2026-10-24T09:00:10Z",
                  "completed_at":"2026-10-24T09:20:00Z",
                  "check_run_url":"https://api.github.com/repos/HMarcusWH/PermanssonLean/check-runs/103"}
        self.check={"id":103,"head_sha":M,"name":auth.JOB,
                    "status":"completed","conclusion":"success",
                    "app":{"slug":"github-actions"}}
        self.artifact={"id":104,"name":auth.ARTIFACT,"expired":False,
                       "digest":"sha256:"+auth.sha(self.file.read_bytes()),
                       "created_at":"2026-10-24T09:19:00Z",
                       "workflow_run":{"id":101,"head_sha":M}}
        self.up_run={"id":201,"head_sha":M,"head_branch":"main",
                     "event":"push","run_attempt":2,
                     "status":"completed","conclusion":"success",
                     "path":auth.UPSTREAM_WORKFLOW,
                     "updated_at":"2026-10-24T08:10:00Z"}
        self.up_job={"id":202,"run_id":201,"head_sha":M,"run_attempt":2,
                     "name":auth.UPSTREAM_JOB,"status":"completed",
                     "conclusion":"success",
                     "started_at":"2026-10-24T08:00:00Z",
                     "completed_at":"2026-10-24T08:06:00Z",
                     "check_run_url":"https://api.github.com/repos/HMarcusWH/PermanssonLean/check-runs/203"}
        self.up_check={"id":203,"head_sha":M,"name":auth.UPSTREAM_JOB,
                       "status":"completed","conclusion":"success",
                       "app":{"slug":"github-actions"}}
        self.up_artifact=upstream_metadata()

    def invoke(self):
        api={"/actions/runs/101":self.run,"/check-runs/103":self.check,
             "/actions/artifacts/104":self.artifact,
             "/actions/runs/201":self.up_run,"/check-runs/203":self.up_check,
             "/actions/artifacts/204":self.up_artifact}
        jobs={"/actions/runs/101/jobs":[self.job],
              "/actions/runs/201/jobs":[self.up_job]}
        with mock.patch.object(auth,"live",side_effect=lambda path:api[path]), \
             mock.patch.object(auth,"paginate",
                               side_effect=lambda path,key:jobs[path]), \
             mock.patch.object(auth,"validate_postseal_payload",
                               return_value={"archive_sha256":auth.sha(b"mock candidate")}):
            return auth.authenticate_postseal(M,PDF,IDS,self.file)

    def test_reproduced_archive_receipt_still_has_no_scholarly_authority(self):
        observed=self.invoke()
        self.assertEqual(observed["status"],"COMPLETE_ARCHIVE_REPLAY")
        self.assertTrue(observed["authenticated_ci_artifact"])
        self.assertFalse(observed["independent_scholarly_approval"])
        self.assertFalse(observed["mathematical_release_approved"])
        self.assertEqual(observed["upstream_preseal"]["run_id"],201)
        self.assertEqual(observed["upstream_preseal"]["artifact_sha256"],
                         UPSTREAM_DIGEST)

    def test_failed_or_stale_upstream_producer_cannot_be_certified(self):
        # Each upstream artifact keeps an authentic digest; only the
        # producer run/job/check/attempt identity distinguishes it.
        for name,edit in (
            ("run-failed",lambda: self.up_run.update(conclusion="failure")),
            ("run-cancelled",lambda: self.up_run.update(conclusion="cancelled")),
            ("run-in-progress",lambda: self.up_run.update(status="in_progress")),
            ("run-wrong-workflow",lambda: self.up_run.update(
                path=".github/workflows/research-lean.yml")),
            ("run-wrong-head",lambda: self.up_run.update(head_sha="f"*40)),
            ("run-pull-request",lambda: self.up_run.update(event="pull_request")),
            ("run-rerun-attempt",lambda: self.up_run.update(run_attempt=3)),
            ("job-failed",lambda: self.up_job.update(conclusion="failure")),
            ("job-other-attempt",lambda: self.up_job.update(run_attempt=1)),
            ("job-renamed",lambda: self.up_job.update(name="other")),
            ("check-failed",lambda: self.up_check.update(conclusion="failure")),
            ("artifact-other-run",lambda: self.up_artifact.update(
                workflow_run={"id":999,"head_sha":M})),
            ("artifact-expired",lambda: self.up_artifact.update(expired=True)),
            ("artifact-earlier-attempt",lambda: self.up_artifact.update(
                created_at="2026-10-24T07:00:00Z")),
            ("artifact-after-job",lambda: self.up_artifact.update(
                created_at="2026-10-24T08:07:00Z")),
            ("finished-after-postseal",lambda: self.up_run.update(
                updated_at="2026-10-24T09:30:00Z")),
        ):
            with self.subTest(fault=name):
                self.setUp()
                edit()
                with self.assertRaises(auth.PostsealAuthenticationError):
                    self.invoke()

    def test_upstream_identity_is_mandatory_and_distinct(self):
        global IDS
        original=IDS
        try:
            for key in ("upstream_run_id","upstream_check_run_id",
                        "upstream_artifact_id"):
                with self.subTest(missing=key):
                    IDS={k:v for k,v in original.items() if k!=key}
                    with self.assertRaises(auth.PostsealAuthenticationError):
                        self.invoke()
            IDS={**original,"upstream_run_id":101}
            with self.assertRaises(auth.PostsealAuthenticationError):
                self.invoke()
        finally:
            IDS=original

    def test_postseal_must_have_replayed_the_authenticated_upstream(self):
        for name,meta in (
            ("digest",{**upstream_metadata(),"digest":"sha256:"+"0"*64}),
            ("artifact",{**upstream_metadata(),"id":205}),
            ("run",{**upstream_metadata(),"workflow_run":{"id":999,"head_sha":M}}),
        ):
            with self.subTest(fault=name):
                self.setUp()
                self.file.write_bytes(artifact_bytes(meta))
                self.artifact["digest"]="sha256:"+auth.sha(self.file.read_bytes())
                with self.assertRaises(auth.PostsealAuthenticationError):
                    self.invoke()

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
