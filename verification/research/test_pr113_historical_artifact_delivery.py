"""PR113 original ZIP downloader: fake API tests, never synthetic approvals."""
import copy
import json
import unittest
from unittest import mock
import pr113_historical_artifact_delivery as d

H="a"*40
B=d.B113
S="b"*40
RUN=301


def context():
    return {"original_base_sha":B,"head_sha":H,"synthetic_sha":S}


def inputs():
    from test_pr113_infrastructure_acceptance import (
        zipped,historical_files,a2_files,synthetic_lake_manifest)
    original={"T":zipped(historical_files()),"A2":zipped(a2_files())}
    run={
        "id":RUN, "head_sha":H,
        "head_branch":"research/final-mathematical-closure",
        "event":"push", "status":"completed", "conclusion":"success",
        "run_attempt":1,"path":d.ACTIVE_WORKFLOW,
    }
    jobs=[]
    artifacts=[]
    checks={}
    sources={}
    for i,kind in enumerate(("T","A2"),1):
        jn,an=d.EXPECTED_ARTIFACTS[kind]
        jobid,aid=500+i,900+i
        checks[kind]=400+i
        jobs.append({
            "id":jobid, "run_id":RUN,"run_attempt":1,"head_sha":H,
            "name":jn,"status":"completed","conclusion":"success",
            "check_run_url":("https://api.github.com/repos/"+d.REPOSITORY+
                             "/check-runs/"+str(checks[kind])),
            "started_at":"2026-10-25T09:00:00Z",
            "completed_at":"2026-10-25T09:40:00Z",
        })
        artifacts.append({
            "id":aid, "name":an, "expired":False,
            "digest":"sha256:"+d.sha(original[kind]),
            "workflow_run":{"id":RUN,"head_sha":H},
            "created_at":"2026-10-25T09:20:00Z",
        })
        sources[aid]=original[kind]
    api={
        f"/actions/runs/{RUN}":run,
        f"/actions/runs/{RUN}/jobs?per_page=100":{"jobs":jobs},
        f"/actions/runs/{RUN}/artifacts?per_page=100":{"artifacts":artifacts},
    }
    return api,sources,json.dumps(synthetic_lake_manifest(),
             sort_keys=True).encode()


def git(*args):
    if args==("rev-parse","HEAD"):
        return S
    if args==("cat-file","-t",H):
        return "commit"
    if args==("show","-s","--format=%P",S):
        return B+" "+H
    if args==("show",H+":lake-manifest.json"):
        return inputs()[2].decode()
    raise AssertionError("unexpected Git op "+repr(args))


class HistoricalDeliveryTests(unittest.TestCase):
    def test_two_original_jobs_and_statuses_never_claim_approval(self):
        api, zips, manifest=inputs()
        with mock.patch.object(d,"authenticate_original_zip",
                               side_effect=lambda kind,ids,raw,head,live:
                                   {"sha256":d.sha(raw)}):
            payload=d.deliver(context(),RUN,77,git=git,
                              live=api.__getitem__,download=zips.__getitem__)
        self.assertEqual(payload["envelope"]["source_bound_ci"],[])
        self.assertEqual(payload["envelope"]["security_review_id"],77)
        self.assertEqual(payload["transport"]["head"],H)
        self.assertEqual(set(payload["zips"]),{"T","A2"})
        self.assertEqual(len(payload["transport"]["originals"]),2)
        self.assertFalse(payload["transport"]["independent_security_review"])
        self.assertFalse(payload["transport"]["owner_merge_authorized"])

    def test_real_artifact_preflight_checks_run_and_metadata(self):
        api,zips,raw=inputs()
        for kind in ("T","A2"):
            selected=d.unique_job_and_artifact(
                api[f"/actions/runs/{RUN}"],
                api[f"/actions/runs/{RUN}/jobs?per_page=100"],
                api[f"/actions/runs/{RUN}/artifacts?per_page=100"],
                kind=kind,head=H)
            self.assertEqual(selected["run_id"],RUN)
            self.assertIsInstance(selected["artifact_id"],int)
        cases=[
            lambda a:a[f"/actions/runs/{RUN}"].update(head_sha="c"*40),
            lambda a:a[f"/actions/runs/{RUN}"].update(conclusion="failure"),
            lambda a:a[f"/actions/runs/{RUN}"].update(event="pull_request"),
            lambda a:a[f"/actions/runs/{RUN}/jobs?per_page=100"]["jobs"][0].update(
                conclusion="failure"),
            lambda a:a[f"/actions/runs/{RUN}/artifacts?per_page=100"]["artifacts"][0].update(
                expired=True),
            lambda a:a[f"/actions/runs/{RUN}/jobs?per_page=100"]["jobs"].append(
                copy.deepcopy(a[f"/actions/runs/{RUN}/jobs?per_page=100"]["jobs"][0])),
        ]
        for mutate in cases:
            data=copy.deepcopy(api)
            mutate(data)
            with self.subTest(mutate=mutate),self.assertRaises(d.DeliveryError):
                d.unique_job_and_artifact(
                    data[f"/actions/runs/{RUN}"],
                    data[f"/actions/runs/{RUN}/jobs?per_page=100"],
                    data[f"/actions/runs/{RUN}/artifacts?per_page=100"],
                    kind="T",head=H)

    def test_invalid_https_redirect_is_rejected(self):
        for url in ("http://api.github.com/artifacts/1",
                    "https://127.0.0.1/latest",
                    "https://169.254.169.254/",
                    "https://notgithubusercontent.com/file",
                    "file:///etc/passwd",
                    "https://api.github.com:8080/foo",
                    "https://user:password@api.github.com/foo"):
            with self.subTest(url=url):
                self.assertFalse(d.approved_https_url(url))
        self.assertTrue(d.approved_https_url(
            "https://pipelines.actions.githubusercontent.com/path"))
        self.assertTrue(d.approved_https_url(
            "https://githubactionsproduction.blob.core.windows.net/path"))

    def test_missing_reviewer_id_and_borrowed_original_sources_rejected(self):
        api,zips,manifest=inputs()
        with self.assertRaises(d.DeliveryError):
            d.deliver(context(),RUN,0,git=git,
                      live=api.__getitem__,download=zips.__getitem__)
        altered=context()
        altered["original_base_sha"]="0"*40
        with self.assertRaises(d.DeliveryError):
            d.deliver(altered,RUN,77,git=git,
                      live=api.__getitem__,download=zips.__getitem__)

    def test_wrong_or_partial_lake_manifest_blocks(self):
        api,zips,m=inputs()
        with self.assertRaises(Exception):
            d.collect(H,RUN,live=api.__getitem__,
                      download=zips.__getitem__,committed_manifest=b"{}")

    def test_detached_main_transport_rejects_foreign_merge_and_bogus_review(self):
        from pr113_historical_postmerge import source_target
        ctx={"original_base_sha":B,
             "reviewed_head_sha":H,"merged_main_sha":S}
        api, zips, manifest=inputs()
        def merged_git(*args):
            if args==("rev-parse","HEAD"):return S
            if args==("show","-s","--format=%P",S):return B+" "+H
            if args==("show",H+":lake-manifest.json"):
                return manifest.decode()
            raise AssertionError(args)
        with mock.patch.object(d,"authenticate_original_zip",
                               side_effect=lambda kind,ids,raw,head,live:
                                   {"sha256":d.sha(raw)}):
            result=d.deliver_merged(ctx,RUN,77,git=merged_git,
                     live=api.__getitem__,download=zips.__getitem__)
        self.assertEqual(result["envelope"]["target"],source_target(ctx))
        self.assertEqual(result["envelope"]["security_review_id"],77)
        self.assertFalse(result["transport"]["owner_merge_authorized"])
        broken=dict(ctx,merged_main_sha="0"*40)
        with self.assertRaises(d.DeliveryError):
            d.deliver_merged(broken,RUN,77,git=merged_git,
                     live=api.__getitem__,download=zips.__getitem())
        with self.assertRaises(d.DeliveryError):
            d.deliver_merged(ctx,RUN,0,git=merged_git,
                     live=api.__getitem__,download=zips.__getitem())



if __name__=="__main__":
    unittest.main()
