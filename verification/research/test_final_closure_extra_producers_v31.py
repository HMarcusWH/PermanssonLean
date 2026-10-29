"""Additional v3.1 producer controls: only real source/CI, no auto-approval."""
import io
import json
import unittest
from unittest import mock
import zipfile

import final_closure_extra_producers_v31 as auth

H="a"*40
ORIGINAL_HASH="d"*64
CASES=[f"C-{n:02}" for n in range(1,46)]
LEGACY=CASES[:20]
CLAIMS=["Q1","Q2","Q3","M1","M2","M3","N1","N2","N3","D8","D9"]


def zip_bytes(members):
    f=io.BytesIO()
    with zipfile.ZipFile(f,"w") as z:
        for name,data in sorted(members.items()):
            z.writestr(name,data)
    return f.getvalue()


def fixture():
    expected=auth.expected_controls(CASES,LEGACY,CLAIMS)
    mapping={
        "original_positive":CASES,
        "legacy_negative":LEGACY,
        "claim_pair":CLAIMS,
    }
    producers=[]
    zipped={}
    endpoints={}
    jobs={}
    approved={}
    for i,(kind,owners) in enumerate(mapping.items(),1):
        run_id,job_id,check_id,artifact_id=i+100,i+200,i+300,i+400
        workflow=f".github/workflows/proposed-control-{kind}.yml"
        job_name=f"real-control-{kind}"
        workflow_sha=(str(i)*40)
        approved[workflow]=workflow_sha
        endpoints["/contents/"+workflow+"?ref="+H]={
            "type":"file","sha":workflow_sha}
        source={}
        owners_index=[]
        for owner in owners:
            receipt={
                "status":auth.STATUS[kind],
                "head_sha":H,
                "case_id" if kind!="claim_pair" else "claim_id":owner,
                "accepted_claim":False,
                "independent_case_review":False,
                "independent_mathematical_review":False,
                "scientific_release_approved":False,
            }
            member=f"receipts/{owner}.json"
            raw=(json.dumps(receipt,sort_keys=True)+"\n").encode()
            source[member]=raw
            owners_index.append({
                "kind":kind,"owner_id":owner,
                "receipt_member":member,"receipt_sha256":auth.sha(raw)})
        index={
            "format":auth.INDEX_FORMAT,
            "head_sha":H,"github_run_id":run_id,
            "github_run_attempt":1,"owners":owners_index,
            "accepted_cases":0,"accepted_claims":0,
            "independent_review":False,
        }
        index_bytes=(json.dumps(index,sort_keys=True)+"\n").encode()
        source["producer_owner_index.json"]=index_bytes
        ZIP=zip_bytes(source)
        zipped[artifact_id]=ZIP
        producers.append({
            "run_id":run_id,"run_attempt":1,"job_id":job_id,
            "check_run_id":check_id,"artifact_id":artifact_id,
            "artifact_name":f"pr113-control-{kind}-source",
            "artifact_sha256":auth.sha(ZIP),
            "workflow_path":workflow,"job_name":job_name,
            "owner_index_member":"producer_owner_index.json",
            "owner_index_sha256":auth.sha(index_bytes),"owners":owners_index})
        endpoints[f"/actions/runs/{run_id}"]={
            "id":run_id,"head_sha":H,"head_branch":auth.BRANCH,
            "run_attempt":1,"status":"completed","conclusion":"success",
            "event":"workflow_dispatch","path":workflow}
        jobs[run_id]=[{
            "id":job_id,"name":job_name,"run_id":run_id,
            "run_attempt":1,"head_sha":H,"status":"completed",
            "conclusion":"success",
            "check_run_url":f"https://api.github.com/repo/check-runs/{check_id}"}]
        endpoints[f"/check-runs/{check_id}"]={
            "id":check_id,"head_sha":H,"name":job_name,
            "status":"completed","conclusion":"success",
            "app":{"slug":"github-actions"}}
        endpoints[f"/actions/artifacts/{artifact_id}"]={
            "id":artifact_id,"name":producers[-1]["artifact_name"],
            "expired":False,"digest":"sha256:"+auth.sha(ZIP),
            "workflow_run":{"id":run_id,"head_sha":H}}
    payload={
        "format":auth.FORMAT,"head_sha":H,
        "original_21_producer_bundle_sha256":ORIGINAL_HASH,
        "original_producing_artifact_count":21,
        "source_controls_accepted":False,
        "independent_security_review":False,
        "mathematical_approval":False,
        "merged_main_sha":None,
        "producers":producers,
    }
    original={
        "format":auth.ORIGINAL_FORMAT,
        "status":"REAL_PRODUCING_BYTES_UNREVIEWED",
        "producer_count":21,"head_sha":H,
    }
    return expected,payload,zipped,endpoints,jobs,original,approved


class ExtraControlProvenanceTests(unittest.TestCase):
    def execute(self,mutate=None):
        expected,contract,binaries,api,jobs,original,approved=fixture()
        if mutate:
            mutate(expected,contract,binaries,api,jobs,original,approved)
        with mock.patch.object(auth,"live",side_effect=lambda path:api[path]), \
             mock.patch.object(auth,"paginate",
                 side_effect=lambda path,key:jobs[int(path.split("/")[3])]):
            return auth.authenticated_extra_controls(
                H,contract,binaries,original_producers=original,
                original_bundle_sha256=ORIGINAL_HASH,
                expected=expected,reviewed_workflow_blobs=approved)

    def test_all_45_20_11_real_job_shapes_source_attributed_not_approved(self):
        report=self.execute()
        self.assertEqual(len(report["source_owned_controls"]),76)
        self.assertEqual(report["original_21_producing_artifacts_still_required"],21)
        self.assertEqual(report["original_case_positives"],45)
        self.assertEqual(report["legacy_case_negatives"],20)
        self.assertEqual(report["claim_positive_negative_pairs"],11)
        self.assertFalse(report["schema_security_approved"])
        self.assertEqual(report["accepted_cases"],0)
        self.assertEqual(report["accepted_claims"],0)
        json.dumps(report)  # source receipt must serialize canonically

    def test_missing_or_borrowed_owner_and_false_source_index_fail(self):
        changes=[
            lambda e,c,b,a,j,o,p:c["producers"][0]["owners"].pop(),
            lambda e,c,b,a,j,o,p:c["producers"][1]["owners"][0].update(
                owner_id="FOREIGN"),
            lambda e,c,b,a,j,o,p:c["producers"][2]["owners"][0].update(
                kind="original_positive"),
            lambda e,c,b,a,j,o,p:c.update(mathematical_approval=True),
            lambda e,c,b,a,j,o,p:c["producers"][0].update(
                check_run_id=c["producers"][1]["check_run_id"]),
            lambda e,c,b,a,j,o,p:b.update({401:b"borrowed bytes"}),
        ]
        for idx,mutation in enumerate(changes):
            with self.subTest(idx=idx),self.assertRaises(
                    (auth.ControlProducerError,ValueError)):
                self.execute(mutation)

    def test_forged_live_workflow_head_run_check_and_zip_digest_fail(self):
        changes=[
            lambda e,c,b,a,j,o,p:a["/actions/runs/101"].update(head_sha="b"*40),
            lambda e,c,b,a,j,o,p:a["/actions/runs/101"].update(
                head_branch="malicious"),
            lambda e,c,b,a,j,o,p:j[101][0].update(conclusion="failure"),
            lambda e,c,b,a,j,o,p:a["/check-runs/301"].update(
                conclusion="failure"),
            lambda e,c,b,a,j,o,p:a["/actions/artifacts/401"].update(
                digest="sha256:"+"e"*64),
            lambda e,c,b,a,j,o,p:p.clear(),
        ]
        for idx,mutation in enumerate(changes):
            with self.subTest(idx=idx),self.assertRaises(
                    (auth.ControlProducerError,ValueError)):
                self.execute(mutation)

    def test_original_21_bound_CI_cannot_be_substituted(self):
        def no_original(e,c,b,a,j,o,p):
            o["producer_count"]=20
        with self.assertRaises(auth.ControlProducerError):
            self.execute(no_original)
        def no_real_source(e,c,b,a,j,o,p):
            a["/contents/.github/workflows/proposed-control-original_positive.yml?ref="+H]["sha"]="f"*40
        with self.assertRaises(auth.ControlProducerError):
            self.execute(no_real_source)


    def test_assembler_calls_real_76_owner_validator_with_original_producers(self):
        """Exercise public assembler, authenticating synthetic owner ZIPs locally."""
        from pathlib import Path
        import tempfile
        import final_closure_authenticate as gh
        import final_closure_case_receipts as original_auth
        import final_closure_schema as schema
        import final_closure_legacy_semantic_evidence as legacy
        import pr113_v31_execution_integrity as integrity
        from test_pr113_v31_execution_integrity import (
            CASE_IDS, complete, source, authentic_original_legacy,
        )
        contract, binaries = complete()
        original = authentic_original_legacy()
        with tempfile.TemporaryDirectory(prefix="pr113-real-callee-") as td:
            root = Path(td)
            zip_dir = root / "additional-zips"
            zip_dir.mkdir()
            for artifact_id, raw in binaries.items():
                (zip_dir / f"{artifact_id}.zip").write_bytes(raw)
            original_file = root / "original.json"
            original_file.write_text(json.dumps({
                "format": "Permansson.FinalClosureDetachedReceipts.v3",
                "head_sha": H, "evidence_bundle_sha256": ORIGINAL_HASH,
            }))
            original_zip = root / "original.zip"
            original_zip.write_bytes(b"test-only original GH ZIP")
            contract_file = root / "contract.json"
            contract_file.write_text(json.dumps(contract))
            blobs_file = root / "workflow-blobs.json"
            blobs_file.write_text("{}")
            case_map = {cid: {} for cid in CASE_IDS}
            candidate = {
                "accepted_cases": 0, "accepted_claims": 0,
                "schema_security_approved": False,
                "independent_mathematical_review": False,
            }
            with mock.patch.object(gh, "git", return_value=H), \
                 mock.patch.object(schema, "validate_overlay"), \
                 mock.patch.object(original_auth, "load_detached_bundle",
                                   return_value={}), \
                 mock.patch.object(original_auth, "authenticate_v3_sources",
                                   return_value=original), \
                 mock.patch.object(legacy, "original_case_map",
                                   return_value=(case_map, set(CASE_IDS[:20]))), \
                 mock.patch.object(auth, "candidate_registry",
                                   return_value=contract["producers"]), \
                 mock.patch.object(auth, "authenticated_extra_controls",
                                   return_value=candidate), \
                 mock.patch.object(integrity, "exact_source",
                                   return_value=source()), \
                 mock.patch.object(integrity, "validate_executed_controls",
                                   wraps=integrity.validate_executed_controls) as validator:
                report = auth.assemble_review_pending(
                    H, original_file, original_zip, contract_file,
                    zip_dir, blobs_file, root / "validated.json")
                self.assertEqual(
                    report["actual_execution_member_validation"]["source_owner_count"],
                    76)
                self.assertEqual(validator.call_count, 1)
                self.assertIs(
                    validator.call_args.kwargs["original_producers"], original)
                self.assertFalse(
                    report["actual_execution_member_validation"]["mathematical_acceptance"])
                original["producers"][555]["members"][
                    "C-01/test-00/raw_compiler/event-1-000001/source.lean"
                ] = b"forged original capture"
                with self.assertRaises(integrity.RealControlError):
                    auth.assemble_review_pending(
                        H, original_file, original_zip, contract_file,
                        zip_dir, blobs_file, root / "rejected.json")

