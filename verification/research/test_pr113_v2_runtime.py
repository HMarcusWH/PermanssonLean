"""V2 T/T2+A2 runtime integration contracts (synthetic fixtures, NO approval).

Never treat these mocks as authenticated historical producer executions. The
actual old T/A2 offline+Lean legs remain separately mandatory.
"""
from __future__ import annotations
import copy
import io
import json
import unittest
from unittest import mock
import zipfile

import infrastructure_acceptance_v2 as infra
import pr113_required_dual_gate_v2 as gate
import pr113_historical_artifact_delivery_v2 as delivery
import pr113_historical_postmerge_v2 as postmerge

B=infra.release_target.B113
H="a"*40
S="b"*40
TREE="c"*40
DIGEST="d"*64


def git_adapter(*args, checked=S, parents=None, same_tree=True):
    result={
        ("rev-parse","HEAD"):checked,
        ("cat-file","-t",checked):"commit",
        ("cat-file","-t",H):"commit",
        ("rev-parse",checked+"^{tree}"):TREE if same_tree else "e"*40,
        ("rev-parse",H+"^{tree}"):TREE,
        ("show","-s","--format=%P",checked):
            (B+" "+H if parents is None else parents),
    }
    return result[args]


def profile(repo,checked,*,phase):
    assert checked in (H,S)
    assert phase=="active"
    return {
        "head_sha":checked,
        "current_reviewed_workflow_count":30,
        "historical_original_workflow_count":25,
        "independent_security_review":False,
        "current_source_profile_sha256":DIGEST,
    }


def zipbytes():
    stream=io.BytesIO()
    with zipfile.ZipFile(stream,"w",zipfile.ZIP_DEFLATED) as archive:
        archive.writestr("stub.json",'{"candidate":true}')
    return stream.getvalue()


def producer_inputs():
    runid=817
    run={"id":runid,"head_sha":H,
         "head_branch":"research/final-mathematical-closure",
         "event":"push","status":"completed","conclusion":"success",
         "run_attempt":2,"path":delivery.ACTIVE_WORKFLOW}
    jobs=[]
    artifacts=[]
    bins={}
    for i,kind in enumerate(("T","A2"),1):
        job_name,artifact_name=delivery.EXPECTED_ARTIFACTS[kind]
        id=925+i
        aid=1025+i
        checks=1100+i
        jobs.append({
            "id":id,"name":job_name,"run_id":runid,
            "run_attempt":2,"head_sha":H,"status":"completed",
            "conclusion":"success","check_run_url":
                "https://api.github.com/repos/"+delivery.REPOSITORY+
                "/check-runs/"+str(checks)})
        artifacts.append({"id":aid,"name":artifact_name,
            "expired":False,"workflow_run":{"id":runid,"head_sha":H}})
        bins[aid]=zipbytes()
    api={
        "/actions/runs/817":run,
        "/actions/runs/817/jobs?per_page=100":{"jobs":jobs},
        "/actions/runs/817/artifacts?per_page=100":{"artifacts":artifacts},
    }
    return api,bins


class V2RuntimeUnitContracts(unittest.TestCase):
    def test_source_profile_requires_actual_H_or_ordered_S_and_equal_tree(self):
        with mock.patch.object(infra,"workflow_audit",side_effect=profile):
            for checked in (H,S):
                observed=infra.checked_profile(
                    H,git=lambda *a:git_adapter(*a,checked=checked))
                self.assertEqual(observed["head_sha"],checked)
            for parents in (H+" "+B,B+" "+"0"*40,B+" "+H+" "+"1"*40):
                with self.subTest(parents=parents):
                    with self.assertRaises(infra.InfrastructureError):
                        infra.checked_profile(
                            H,git=lambda *a:git_adapter(*a,parents=parents))
            with self.assertRaises(infra.InfrastructureError):
                infra.checked_profile(
                    H,git=lambda *a:git_adapter(*a,same_tree=False))
            with self.assertRaises(infra.InfrastructureError):
                infra.checked_profile(H,git=lambda *a:
                    "blob" if a==("cat-file","-t",S) else git_adapter(*a))

    def test_v2_transport_reads_only_v2_event_adapters(self):
        self.assertIs(delivery.actual_ci_event,gate.actual_ci_event)
        self.assertEqual(infra.FORMAT,"Permansson.PR113.InfrastructureEvidence.v2")
        self.assertEqual(delivery.EVIDENCE_FORMAT,infra.FORMAT)
        self.assertEqual(postmerge.FORMAT,
                         "Permansson.PR113.PostmergeHistoricalEvidence.v2")

    def test_v2_collector_requires_two_distinct_verified_producer_jobs(self):
        api,bins=producer_inputs()
        with mock.patch.object(delivery,"authenticate_original_zip",
                               side_effect=lambda kind,src,raw,head,live:
                               {"status":"UNAPPROVED_VERIFIED","kind":kind}),\
             mock.patch.object(delivery,"inspect_zip",
                               return_value={"test.json":b'{}'}),\
             mock.patch.object(delivery,"inspect_T",
                               return_value={"candidate":"T"}),\
             mock.patch.object(delivery,"inspect_A2",
                               return_value={"candidate":"A2"}),\
             mock.patch.object(delivery,"verify_A2_dependency_bridge",
                               return_value="f"*64):
            zips, ids, reports = delivery.collect(
                H,817,live=api.__getitem__,download=bins.__getitem__,
                committed_manifest=b"pinned immutable manifest")
            self.assertEqual(set(zips),{"T","A2"})
            self.assertNotEqual(ids["T"]["job_id"],ids["A2"]["job_id"])
            self.assertNotEqual(ids["T"]["artifact_id"],ids["A2"]["artifact_id"])
            self.assertEqual(reports["A2"]["scope"]["dependency_bridge_sha256"],
                             "f"*64)
            altered=copy.deepcopy(api)
            altered["/actions/runs/817"]["run_attempt"]=1
            with self.assertRaises(delivery.DeliveryError):
                delivery.collect(H,817,live=altered.__getitem__,
                                 download=bins.__getitem__,
                                 committed_manifest=b"pinned immutable manifest")
            altered=copy.deepcopy(api)
            altered["/actions/runs/817/jobs?per_page=100"]["jobs"][1]["id"] = \
                 altered["/actions/runs/817/jobs?per_page=100"]["jobs"][0]["id"]
            with self.assertRaises(delivery.DeliveryError):
                delivery.collect(H,817,live=altered.__getitem__,
                                 download=bins.__getitem__,
                                 committed_manifest=b"pinned immutable manifest")

    def test_v2_required_check_rejects_v1_receipt_even_with_status(self):
        ctx={"original_base_sha":B,"head_sha":H,
             "synthetic_sha":S,"github_run_id":123,
             "github_run_attempt":1,"github_job":"research",
             "event_sha256":"e"*64}
        def candidate():
            return {
                "format":"Permansson.PR113.HistoricalDualRequiredSourceReceipt.v2",
                "status":
                "HISTORICAL_T_AND_A2_GENUINE_WITH_INDEPENDENT_SECURITY_REVIEW",
                "source_head":H,
                "historical_original_workflow_count":25,
                "current_reviewed_workflow_count":30,
                "workflow_profile_sha256":DIGEST,
                "historical_source_and_security_review_authenticated":True,
                "required_ci_successful":0,
                "merge_authorized":False,
                "publication_authorized":False,
                "independent_mathematical_review":False,
                "genuine_artifacts":{"T":{},"A2":{}},
                "T_execution":{},"A2_execution":{},
            }
        with mock.patch.object(gate,"actual_ci_event",return_value=ctx):
            original=candidate()
            result=gate.verify({"target":{"base_sha":B,"head_sha":H,
                                         "synthetic_sha":S}},
                               b"t",b"a",
                               env={"GITHUB_EVENT_NAME":"pull_request"},
                               historical_gate=lambda *a:original)
            self.assertFalse(result["all_required_CI_accepted"])
            for field,value in (("format",
                                 "Permansson.PR113.HistoricalDualRequiredSourceReceipt.v1"),
                                ("current_reviewed_workflow_count",25),
                                ("historical_original_workflow_count",30),
                                ("workflow_profile_sha256","bad"),
                                ("required_ci_successful",1)):
                forged=dict(candidate(),**{field:value})
                with self.subTest(field=field),\
                     self.assertRaises(gate.RequiredGateError):
                    gate.verify({"target":{"base_sha":B,"head_sha":H,
                                                 "synthetic_sha":S}},
                                b"t",b"a",
                                env={"GITHUB_EVENT_NAME":"pull_request"},
                                historical_gate=lambda *a:forged)

    def test_v2_historical_review_requires_real_external_policy(self):
        # An empty source-owned roster is NOT a nonauthor GitHub review.
        with self.assertRaises(infra.InfrastructureError):
            infra.authority_policy(H,git=lambda *a:
                '{"format":"Permansson.InfrastructureReviewerAuthority.v1",'
                '"status":"UNCONFIGURED","owner":"HMarcusWH","reviewers":[]}')
