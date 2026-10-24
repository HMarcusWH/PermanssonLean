"""Mock adversaries for real producer-byte authentication; not real review."""
import io
import json
import unittest
from unittest import mock
import zipfile
import final_closure_producer_bytes as unit
from final_closure_candidate_artifact_auth import KINDS

H = "a"*40

def zip_payload(members):
    f = io.BytesIO()
    with zipfile.ZipFile(f, "w") as z:
        for name, body in members.items():
            z.writestr(name, body)
    return f.getvalue()

def fixture():
    index, binary, urls, jobs = [], {}, {}, {}
    for kind in ("compiler", "append", "legacy"):
        spec = KINDS[kind]
        for shard in range(spec["count"]):
            seq = len(index)+1
            run, job, check, artifact = (
                10000+seq, 20000+seq, 30000+seq, 40000+seq)
            manifest = json.dumps({"kind":kind,"shard":shard}).encode()
            raw = zip_payload({spec["manifest"]:manifest,
                               "source.log":b"actual source evidence"})
            rec = {
                "format":"Permansson.PR113.AuthenticatedProducerArtifact.v1",
                "status":"CI_ARTIFACT_DIGEST_VERIFIED_UNREVIEWED",
                "head_sha":H, "workflow_path":spec["workflow"],
                "run_id":run, "run_attempt":1, "job_id":job,
                "actual_check_run_id":check, "artifact_id":artifact,
                "artifact_name":spec["artifact"]+str(shard),
                "artifact_sha256":unit.sha(raw),
                "manifest_sha256":unit.sha(manifest),
                "mathematical_acceptance":False,
                "independent_review":False, "scientific_release_approved":False,
                "merged_main_sha":None,
            }
            index.append(rec)
            binary[artifact]=raw
            urls[f"/actions/runs/{run}"]={
                "id":run,"head_sha":H,"run_attempt":1,
                "status":"completed","conclusion":"success",
                "event":"push","path":spec["workflow"]}
            jobs[run]=[{
                "id":job, "name":spec["job"]+f" ({shard})",
                "head_sha":H,"run_attempt":1,"conclusion":"success",
                "check_run_url":f"https://api.github.com/repos/HMarcusWH/PermanssonLean/check-runs/{check}"}]
            urls[f"/check-runs/{check}"]={
                "id":check,"head_sha":H,"name":spec["job"]+f" ({shard})",
                "status":"completed","conclusion":"success",
                "app":{"slug":"github-actions"}}
            urls[f"/actions/artifacts/{artifact}"]={
                "id":artifact,"name":spec["artifact"]+str(shard),
                "expired":False,"digest":"sha256:"+unit.sha(raw),
                "workflow_run":{"id":run,"head_sha":H}}
    return index, binary, urls, jobs

class ProducerByteTests(unittest.TestCase):
    def execute(self, mutate=None):
        index, binary, urls, jobs = fixture()
        if mutate:mutate(index,binary,urls,jobs)
        with mock.patch.object(unit, "live", side_effect=lambda p:urls[p]), \
             mock.patch.object(unit, "paginate",
                               side_effect=lambda p, key: jobs[int(p.split("/")[3])]):
            return unit.authenticate(H,index,binary)

    def test_exact_21_producers_are_not_review_or_release(self):
        record=self.execute()
        self.assertEqual(record["producer_count"],21)
        self.assertEqual(record["accepted_cases"],0)
        self.assertFalse(record["release_approved"])
        for artifact,p in record["producers"].items():
            got=unit.original_member(
                record,artifact,p["check_run_id"],
                "source.log",unit.sha(b"actual source evidence"))
            self.assertEqual(got,b"actual source evidence")

    def test_stale_job_borrowed_check_and_zip_tamper_reject(self):
        changes=[
            lambda a,b,c,d:b.pop(40001),
            lambda a,b,c,d:a[0].update(
                actual_check_run_id=a[1]["actual_check_run_id"]),
            lambda a,b,c,d:c["/actions/runs/10001"].update(head_sha="b"*40),
            lambda a,b,c,d:b.update({40001:b"tampered"}),
        ]
        for n,change in enumerate(changes):
            with self.subTest(n=n),self.assertRaises(
                    (unit.ProducerBytesError,ValueError)):
                self.execute(change)

    def test_altered_receipt_member_and_borrowed_ids_reject(self):
        record=self.execute()
        for check,hash_ in [(30002,unit.sha(b"actual source evidence")),
                             (30001,"f"*64)]:
            with self.subTest(check=check),self.assertRaises(unit.ProducerBytesError):
                unit.original_member(record,40001,check,"source.log",hash_)

    def test_zip_duplicate_and_unsafe_names_reject(self):
        for contents in [
            {"../bad":b"x"},{"../bad2":b"x"},
            {"dir/FILE":b"x","dir/file":b"x"},
        ]:
            with self.subTest(contents=list(contents)),self.assertRaises(
                    unit.ProducerBytesError):
                unit.inspect_zip(zip_payload(contents))
