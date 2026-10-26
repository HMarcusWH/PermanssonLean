"""Adversarial runtime catalog test: no one can precommit future GH artifact IDs."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import pr113_original21_live_catalog as source

H="a"*40


def fixture():
    runs={};jobs={};artifacts={};checks=[];binary={}
    for i,(kind,spec) in enumerate(sorted(source.KINDS.items())):
        runid=100+i
        runs[runid]={
            "id":runid,"head_sha":H,
            "head_branch":"research/final-mathematical-closure",
            "event":"push","status":"completed","conclusion":"success",
            "run_attempt":2,"path":spec["workflow"],
        }
        jobs[runid]=[];artifacts[runid]=[]
        for shard in range(spec["count"]):
            jobid=1000+100*i+shard
            checkid=2000+100*i+shard
            artifactid=3000+100*i+shard
            artifact_name=spec["artifact"]+str(shard)
            raw=b"Original-source-opaque-unreviewed-"+artifact_name.encode()
            binary[artifactid]=raw
            check={
                "id":checkid,"head_sha":H,
                "app":{"slug":"github-actions"},
                "name":spec["job"]+f" ({shard})",
                "status":"completed","conclusion":"success",
                "details_url":
                    f"https://github.com/HMarcusWH/PermanssonLean/actions/runs/{runid}/job/{jobid}",
            }
            checks.append(check)
            jobs[runid].append({
                "id":jobid,"name":check["name"],
                "head_sha":H,"run_id":runid,"run_attempt":2,
                "status":"completed","conclusion":"success",
                "check_run_url":
                    f"https://api.github.com/repos/HMarcusWH/PermanssonLean/check-runs/{checkid}",
                "started_at":"2026-10-24T12:00:00Z",
                "completed_at":"2026-10-24T12:30:00Z",
            })
            artifacts[runid].append({
                "id":artifactid,"name":artifact_name,
                "expired":False,
                "digest":"sha256:"+hashlib.sha256(raw).hexdigest(),
                "workflow_run":{"id":runid,"head_sha":H},
                "created_at":"2026-10-24T12:05:00Z",
            })
    return checks,runs,jobs,artifacts,binary


class ActualSourceProducerCatalogTests(unittest.TestCase):
    def test_full_21_matrix_maps_are_exact(self):
        checks,*_=fixture()
        latest=source.classify_latest(checks,H)
        self.assertEqual(len(latest),21)
        self.assertEqual(
            len([key for key in latest if key[0]=="compiler"]),4)
        self.assertEqual(
            len([key for key in latest if key[0]=="append"]),9)
        self.assertEqual(
            len([key for key in latest if key[0]=="legacy"]),8)

    def test_missing_one_or_latest_failed_never_borrows_old_success(self):
        checks,*_=fixture()
        with self.assertRaises(source.DiscoveryError):
            source.classify_latest(checks[1:],H)
        checks,*_=fixture()
        latest=dict(checks[0],id=checks[0]["id"]+100000,
                    conclusion="failure")
        with self.assertRaises(source.DiscoveryError):
            source.classify_latest(checks+[latest],H)

    def test_wrong_head_job_attempt_or_workflow_rejected(self):
        checks,runs,jobs,artifacts,binary=fixture()
        first=checks[0];rid=int(source.RUN_URL.fullmatch(
            first["details_url"]).group(1))
        kind,shard=next((key for key in source.classify_latest(checks,H)
                         if source.classify_latest(checks,H)[key] is first))
        for corruption in ("head","attempt","workflow","job","artifact"):
            r=dict(runs[rid]);j=[dict(x) for x in jobs[rid]]
            a=[dict(x) for x in artifacts[rid]]
            if corruption=="head":r["head_sha"]="b"*40
            if corruption=="attempt":j[0]["run_attempt"]=1
            if corruption=="workflow":r["path"]=".github/workflows/research-lean.yml"
            if corruption=="job":j[0]["conclusion"]="failure"
            if corruption=="artifact":
                a[0]["created_at"]="2026-10-24T13:00:00Z"
            with self.subTest(corruption=corruption):
                with self.assertRaises(source.DiscoveryError):
                    source.validate_run_job_artifact(
                        head=H,kind=kind,shard=shard,check=first,
                        run=r,jobs=j,artifacts=a)

    def test_complete_catalog_is_detached_and_never_approval(self):
        checks,runs,jobs,artifacts,binary=fixture()
        def pagination(path,*,key):
            if path.startswith("/commits/"):return checks
            rid=int(path.split("/")[3])
            return jobs[rid] if key=="jobs" else artifacts[rid]
        def lookup(path):return runs[int(path.split("/")[-1])]
        with tempfile.TemporaryDirectory(prefix="perm-catalog-fixture-") as td:
            path=Path(td)/"out"
            with mock.patch.object(source,"git_head",return_value=H):
                result=source.collect(
                    H,path, checks=checks, lookup=lookup,
                    paginate_source=pagination,
                    download=lambda aid: binary[aid])
            self.assertEqual(len(result["artifacts"]),21)
            self.assertEqual(len(list(path.glob("*.zip"))),21)
            self.assertEqual(
                json.loads((path/"source_execution_provenance.json").read_text())
                ["independent_case_review"],False)
            self.assertEqual(json.loads(
                (path/"original21_catalog.json").read_text())["head_sha"],H)

    def test_authentic_frozen_head_manual_dispatch_is_a_producer(self):
        """workflow_dispatch is an original GH run, not manual approval."""
        checks, runs, jobs, artifacts, binary = fixture()
        for run in runs.values():
            run["event"] = "workflow_dispatch"

        def pages(path, *, key):
            if path.startswith("/commits/"):
                return checks
            run_id = int(path.split("/")[3])
            return jobs[run_id] if key == "jobs" else artifacts[run_id]

        def details(path):
            return runs[int(path.split("/")[-1])]

        with tempfile.TemporaryDirectory(prefix="perm-dispatched21-") as td:
            output = Path(td) / "unreviewed"
            with mock.patch.object(source, "git_head", return_value=H):
                report = source.collect(
                    H, output, checks=checks, lookup=details,
                    paginate_source=pages, download=lambda aid: binary[aid])
            self.assertEqual(len(report["artifacts"]), 21)
            self.assertFalse(report["independent_case_review"])
            self.assertEqual(len(list(output.glob("*.zip"))), 21)
            self.assertEqual(
                json.loads((output/"original21_catalog.json").read_bytes())
                ["head_sha"], H)

    def test_dispatch_still_rejects_foreign_event_head_and_branch(self):
        checks, runs, jobs, artifacts, binary = fixture()
        first = checks[0]
        run_id = int(source.RUN_URL.fullmatch(
            first["details_url"]).group(1))
        key = next(k for k, value in source.classify_latest(
            checks, H).items() if value is first)
        kind, shard = key
        valid = dict(runs[run_id], event="workflow_dispatch")
        candidate = source.validate_run_job_artifact(
            head=H, kind=kind, shard=shard, check=first,
            run=valid, jobs=jobs[run_id], artifacts=artifacts[run_id])
        self.assertEqual(candidate["run_id"], run_id)
        self.assertEqual(candidate["kind"], kind)
        for mutation in (
            lambda p: p.update(event="repository_dispatch"),
            lambda p: p.update(event="pull_request"),
            lambda p: p.update(event="schedule"),
            lambda p: p.update(event=None),
            lambda p: p.update(head_sha="0" * 40),
            lambda p: p.update(head_branch="main"),
            lambda p: p.update(path=".github/workflows/research-lean.yml"),
            lambda p: p.update(conclusion="failure"),
            lambda p: p.update(run_attempt=3),
        ):
            with self.subTest(mutation=mutation):
                wrong = dict(valid)
                mutation(wrong)
                with self.assertRaises(source.DiscoveryError):
                    source.validate_run_job_artifact(
                        head=H, kind=kind, shard=shard, check=first,
                        run=wrong, jobs=jobs[run_id],
                        artifacts=artifacts[run_id])

    def test_wrong_artifact_digest_aborts_without_output(self):
        checks,runs,jobs,artifacts,binary=fixture()
        def pagination(path,*,key):
            if path.startswith("/commits/"):return checks
            rid=int(path.split("/")[3])
            return jobs[rid] if key=="jobs" else artifacts[rid]
        with tempfile.TemporaryDirectory(prefix="perm-digest-fixture-") as td:
            destination=Path(td)/"out"
            with mock.patch.object(source,"git_head",return_value=H):
                with self.assertRaises(source.DiscoveryError):
                    source.collect(
                        H,destination,checks=checks,
                        lookup=lambda path:runs[int(path.split("/")[-1])],
                        paginate_source=pagination,
                        download=lambda aid: b"TAMPERED")
            self.assertFalse(destination.exists())

    def test_no_source_head_substitution(self):
        checks,*_=fixture()
        with self.assertRaises(source.DiscoveryError):
            source.classify_latest(checks,"b"*40)


if __name__=="__main__":
    unittest.main()
