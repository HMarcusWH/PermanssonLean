"""Postseal GitHub job/ZIP authentication adversaries; mock-only not approval."""
import io
import json
from pathlib import Path
import random
import stat
import tempfile
import types
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

def artifact_bytes(metadata=None, *, candidate=b"mock candidate",
                   sidecar=b"mock sidecar", receipt=None):
    out=io.BytesIO()
    with zipfile.ZipFile(out,"w") as z:
        z.writestr(auth.UPSTREAM_METADATA,json.dumps(
            upstream_metadata() if metadata is None else metadata))
        z.writestr("candidate/Permansson_Mathematical_Closure_CANDIDATE.zip",
                   candidate)
        z.writestr("candidate/SHA256SUMS.txt",sidecar)
        z.writestr("postseal_replay_receipt.json",json.dumps(receipt if receipt is not None else {
            "format":"Permansson.MathClosure.PostsealReplayCandidate.v1",
            "status":"CANDIDATE_ARCHIVE_REPLAYED_UNREVIEWED",
            "source_commit_sha":M,"head_sha":"c"*40,
            "pdf_sha256":PDF,
            "archive_sha256":auth.sha(candidate),
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

    def invoke(self, *, merged=M, pdf=PDF, actual_payload=False):
        api={"/actions/runs/101":self.run,"/check-runs/103":self.check,
             "/actions/artifacts/104":self.artifact,
             "/actions/runs/201":self.up_run,"/check-runs/203":self.up_check,
             "/actions/artifacts/204":self.up_artifact}
        jobs={"/actions/runs/101/jobs":[self.job],
              "/actions/runs/201/jobs":[self.up_job]}
        with mock.patch.object(auth,"live",side_effect=lambda path:api[path]), \
             mock.patch.object(auth,"paginate",
                               side_effect=lambda path,key:jobs[path]):
            if actual_payload:
                return auth.authenticate_postseal(merged,pdf,IDS,self.file)
            with mock.patch.object(auth,"validate_postseal_payload",
                               return_value={"archive_sha256":auth.sha(b"mock candidate")}):
                return auth.authenticate_postseal(merged,pdf,IDS,self.file)

    def test_large_real_candidate_replays_with_only_github_identity_mocked(self):
        """Actual >4MiB nested ZIP and two real replays; no real approval."""
        from test_final_release_manifest import FullArchiveDigestBindingTests
        from final_closure_producer_bytes import inspect_zip, ProducerBytesError
        fixture=FullArchiveDigestBindingTests(
            "test_full_release_rejects_different_rehashed_zip_with_same_reviewed_fields")
        self.addCleanup(fixture.doCleanups)
        fixture.setUp()
        with zipfile.ZipFile(fixture.archive) as zipped:
            members={name:zipped.read(name) for name in zipped.namelist()}
        # A deterministic, unreviewed evidence ZIP keeps the candidate above
        # the small producer-log budget even when the candidate is compressed.
        bundle=io.BytesIO()
        with zipfile.ZipFile(bundle,"w",compression=zipfile.ZIP_STORED) as zipped:
            zipped.writestr("SYNTHETIC_UNREVIEWED_EVIDENCE.bin",
                            random.Random(113).randbytes(5*1024*1024))
        members["detached_proof_mutation_bundle.zip"]=bundle.getvalue()
        manifest=json.loads(members["approved_seal.json"])
        receipts=json.loads(members["source_acceptance_receipts.json"])
        manifest["evidence_bundle_sha256"]=auth.sha(bundle.getvalue())
        receipts["evidence_bundle_sha256"]=manifest["evidence_bundle_sha256"]
        members["source_acceptance_receipts.json"]=json.dumps(receipts).encode()
        manifest["source_receipts_sha256"]=auth.sha(members["source_acceptance_receipts.json"])
        members["approved_seal.json"]=json.dumps(manifest).encode()
        candidate_dir=fixture.base/"large-synthetic-candidate"
        candidate_dir.mkdir()
        candidate=candidate_dir/"Permansson_Mathematical_Closure_CANDIDATE.zip"
        with zipfile.ZipFile(candidate,"w",compression=zipfile.ZIP_DEFLATED) as zipped:
            for name,raw in sorted(members.items()):
                entry=zipfile.ZipInfo(name,(1980,1,1,0,0,0))
                entry.external_attr=0o100644<<16
                zipped.writestr(entry,raw,compress_type=zipfile.ZIP_DEFLATED)
        original=candidate.read_bytes()
        self.assertGreater(len(original),4*1024*1024)
        sidecar=candidate_dir/"SHA256SUMS.txt"
        sidecar.write_bytes((auth.sha(original)+"  "+candidate.name+"\n"+
                             auth.sha(members["approved_seal.json"])+
                             "  approved_seal.json\n").encode())
        from postseal_replay import replay
        receipt=replay(candidate,sidecar,fixture.base/"first-replay/receipt.json")
        merged,pdf=receipt["source_commit_sha"],receipt["pdf_sha256"]
        for record in (self.run,self.job,self.check,self.up_run,self.up_job,self.up_check,
                       self.artifact["workflow_run"],self.up_artifact["workflow_run"]):
            record["head_sha"]=merged
        raw=artifact_bytes(self.up_artifact,candidate=original,
                           sidecar=sidecar.read_bytes(),receipt=receipt)
        self.file.write_bytes(raw)
        self.artifact["digest"]="sha256:"+auth.sha(raw)
        # The original 21-producer reader retains its original 4MiB budget.
        with self.assertRaises(ProducerBytesError):
            inspect_zip(raw)
        observed=self.invoke(merged=merged,pdf=pdf,actual_payload=True)
        self.assertEqual(observed["archive_sha256"],auth.sha(original))
        self.assertEqual(observed["artifact_sha256"],auth.sha(raw))
        self.assertFalse(observed["independent_scholarly_approval"])
        self.assertFalse(observed["mathematical_release_approved"])

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


class PostsealZipBudgetTests(unittest.TestCase):
    """Real small envelopes plus labelled declared-size fault fixtures."""

    def rows(self, raw):
        with zipfile.ZipFile(io.BytesIO(raw)) as zipped:
            return zipped.infolist()

    def test_candidate_budget_matches_real_replay_without_widening_metadata(self):
        from pathlib import Path
        import sys
        release=Path(__file__).resolve().parents[2]/"release/mathematical-closure-1"
        if str(release) not in sys.path:
            sys.path.insert(0,str(release))
        from postseal_replay import MAX_ARCHIVE_BYTES
        self.assertEqual(auth.MAX_CANDIDATE_BYTES,MAX_ARCHIVE_BYTES)
        self.assertEqual(auth.MAX_METADATA_BYTES,4*1024*1024)
        self.assertEqual(auth.MAX_EXPANDED_BYTES,
                         MAX_ARCHIVE_BYTES+3*auth.MAX_METADATA_BYTES)
        self.assertGreater(auth.MAX_POSTSEAL_ZIP_BYTES,64*1024*1024)
        self.assertGreater(auth.MAX_POSTSEAL_ZIP_BYTES,auth.MAX_EXPANDED_BYTES)
        self.assertEqual(set(auth.inspect_postseal_zip(artifact_bytes())),
                         auth.POSTSEAL_MEMBERS)

    def test_declared_oversized_members_reject_before_any_decompression(self):
        raw=artifact_bytes()
        for name,limit in ((auth.CANDIDATE_MEMBER,auth.MAX_CANDIDATE_BYTES),
                           (auth.UPSTREAM_METADATA,auth.MAX_METADATA_BYTES)):
            rows=self.rows(raw)
            next(row for row in rows if row.filename==name).file_size=limit+1
            with self.subTest(member=name), mock.patch.object(
                    zipfile.ZipFile,"infolist",return_value=rows), \
                    mock.patch.object(zipfile.ZipFile,"open") as decompress:
                with self.assertRaisesRegex(auth.PostsealAuthenticationError,"expansion"):
                    auth.inspect_postseal_zip(raw)
                decompress.assert_not_called()

    def test_candidate_above_64mib_reaches_bounded_read_without_large_allocation(self):
        # SYNTHETIC central-directory declaration tests budget routing only.
        # The deliberately short stream must fail, rather than attest replay.
        raw=artifact_bytes()
        rows=self.rows(raw)
        rows.sort(key=lambda row:row.filename!=auth.CANDIDATE_MEMBER)
        rows[0].file_size=65*1024*1024
        stream=mock.MagicMock()
        stream.__enter__.return_value.read.return_value=b"SYNTHETIC_SHORT_STREAM"
        with mock.patch.object(zipfile.ZipFile,"infolist",return_value=rows), \
                mock.patch.object(zipfile.ZipFile,"open",return_value=stream) as decompress:
            with self.assertRaisesRegex(auth.PostsealAuthenticationError,"length mismatch"):
                auth.inspect_postseal_zip(raw)
        decompress.assert_called_once_with(rows[0])
        stream.__enter__.return_value.read.assert_called_once_with(65*1024*1024+1)

    def test_raw_file_size_bound_precedes_open_or_read_bytes(self):
        path=Path("SYNTHETIC_declared_transport.zip")
        for size in (0,auth.MAX_POSTSEAL_ZIP_BYTES+1):
            with self.subTest(size=size), mock.patch.object(
                    Path,"stat",return_value=types.SimpleNamespace(st_size=size)), \
                    mock.patch.object(Path,"open") as opened, \
                    mock.patch.object(Path,"read_bytes") as unbounded:
                with self.assertRaisesRegex(auth.PostsealAuthenticationError,"before reading"):
                    auth.read_postseal_zip(path)
                opened.assert_not_called()
                unbounded.assert_not_called()

    def test_raw_file_read_is_bounded_and_rejects_growth_or_truncation(self):
        for declared,content in ((3,b"raw"),(2,b"raw"),(4,b"raw"),(65*1024*1024,b"raw")):
            stream=mock.MagicMock()
            stream.__enter__.return_value.read.return_value=content
            with self.subTest(declared=declared), mock.patch.object(
                    Path,"stat",return_value=types.SimpleNamespace(st_size=declared)), \
                    mock.patch.object(Path,"open",return_value=stream):
                if declared==len(content):
                    self.assertEqual(auth.read_postseal_zip(Path("SYNTHETIC.zip")),content)
                else:
                    with self.assertRaisesRegex(auth.PostsealAuthenticationError,"size changed"):
                        auth.read_postseal_zip(Path("SYNTHETIC.zip"))
            stream.__enter__.return_value.read.assert_called_once_with(declared+1)

    def test_unsafe_aliases_modes_and_wrong_inventory_are_rejected(self):
        names=sorted(auth.POSTSEAL_MEMBERS)
        faults=("absolute","traversal","backslash","noncanonical","directory",
                "symlink","nonregular","case_collision","ancestor","extra","missing")
        for fault in faults:
            modified=list(names)
            mode=stat.S_IFREG|0o644
            if fault=="absolute": modified[0]="/candidate.zip"
            elif fault=="traversal": modified[0]="../candidate.zip"
            elif fault=="backslash": modified[0]="candidate\\candidate.zip"
            elif fault=="noncanonical": modified[0]="candidate/./candidate.zip"
            elif fault=="directory": modified[0]="candidate/"
            elif fault=="symlink": mode=stat.S_IFLNK|0o777
            elif fault=="nonregular": mode=stat.S_IFIFO|0o644
            elif fault=="case_collision": modified[0]=modified[1].upper()
            elif fault=="ancestor": modified[0]="candidate"
            elif fault=="extra": modified.append("unexpected.txt")
            elif fault=="missing": modified.pop()
            out=io.BytesIO()
            with zipfile.ZipFile(out,"w") as zipped:
                for index,name in enumerate(modified):
                    entry=zipfile.ZipInfo(name)
                    entry.external_attr=(mode if index==0 else stat.S_IFREG|0o644)<<16
                    zipped.writestr(entry,b"SYNTHETIC")
            with self.subTest(fault=fault), self.assertRaises(auth.PostsealAuthenticationError):
                auth.inspect_postseal_zip(out.getvalue())

    def test_encrypted_member_declares_failure_before_decompression(self):
        raw=artifact_bytes()
        rows=self.rows(raw)
        rows[0].flag_bits|=1
        with mock.patch.object(zipfile.ZipFile,"infolist",return_value=rows), \
                mock.patch.object(zipfile.ZipFile,"open") as decompress:
            with self.assertRaises(auth.PostsealAuthenticationError):
                auth.inspect_postseal_zip(raw)
            decompress.assert_not_called()

    def test_raw_backslash_alias_cannot_normalize_into_expected_member(self):
        # Mutate both local/central filenames after ZIP creation: on Windows,
        # ZipInfo.filename normalizes this alias, but orig_filename retains it.
        raw=artifact_bytes()
        canonical=auth.CANDIDATE_MEMBER.encode()
        alias=auth.CANDIDATE_MEMBER.replace("/","\\",1).encode()
        self.assertEqual(raw.count(canonical),2)
        malformed=raw.replace(canonical,alias)
        with self.assertRaises(auth.PostsealAuthenticationError):
            auth.inspect_postseal_zip(malformed)

    def test_bad_crc_and_invalid_zip_fail_closed(self):
        raw=bytearray(artifact_bytes())
        first=self.rows(bytes(raw))[0]
        offset=first.header_offset+30+len(first.filename.encode())+len(first.extra)
        raw[offset]^=1
        for damaged in (bytes(raw),b"not a ZIP"):
            with self.subTest(crc=damaged!=b"not a ZIP"), \
                    self.assertRaises(auth.PostsealAuthenticationError):
                auth.inspect_postseal_zip(damaged)
