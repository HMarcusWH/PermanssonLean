"""Staged T/H engineering evidence can never satisfy the active-30 gate."""
import json
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest import mock

import pr113_archive_pre_activation_rehearsal_v1 as rehearsal
import pr113_dual_tooling_candidate_v2 as actual

H = "a"*40


def fixture():
    old = {
        "format":"Permansson.Hardening.Check.v1","status":"PASS",
        "check":"archive-reproducibility","context":{"scope":"accepted_artifact_replay"},
        "details":{"acceptance_scope":"accepted_artifact_replay_only",
                   "isolation":{"network_isolation":"ENFORCED",
                                "capabilities":"all_zero"}},
    }
    now = {
        "format":"Permansson.Hardening.Tests.v1","schema_version":1,
        "status":"PASS","suite":"workflow","methods_run":17,
        "execution_tracked_clean":True,"failures":0,"errors":0,"skips":0,
        "covered_requirements":["CI-06","CI-07"],
        "context":{"repository":"HMarcusWH/PermanssonLean",
                   "checked_sha":H,"checked_tree":"e"*40,"event":"local"},
    }
    profile = {
        "format":"Permansson.PR113.ToolingMigrationCandidate.v2",
        "status":"T2_EXACT_SOURCE_REVIEW_PENDING",
        "source_commit_sha":H,"reviewed_workflow_source_mode":"staged",
        "historical_original_workflow_count":25,"current_reviewed_workflow_count":30,
        "historical_packaged_tooling_files_verified":35,
        "historical_archive_unchanged":True,
        "new_successor_T_approved":False,"owner_activation_authorized":False,
        "independent_security_review":False,"workflow_profile_sha256":"e"*64,
        "historical_supplement_tree":"f"*40,
        "historical_manifest_sha256":"d"*64,
        "changed_canonical_tooling":[
            {"path":"verification/integrity/workflow_contract.py",
             "T_blob":"a"*40,"H_blob":"b"*40},
            {"path":"verification/integrity/tests/test_workflow.py",
             "T_blob":"c"*40,"H_blob":"d"*40},
        ],
    }
    return old,now,profile


class StagedRehearsalTests(unittest.TestCase):
    def test_complete_staged_rehearsal_is_never_the_real_active_30(self):
        old,now,profile=fixture()
        result = rehearsal.validate_reports(old,now,profile,H)
        self.assertEqual(result["status"],rehearsal.STATUS)
        self.assertFalse(result["active_30_reverified"])
        self.assertFalse(result["genuine_required_ci"])
        self.assertFalse(result["independent_security_review"])
        with self.assertRaises(actual.DualToolingError):
            actual.validate_dual_reports_v2(
                old,now,T_source=actual.T,H_source=H,profile=profile)

    def test_faulted_isolation_source_test_or_review_field_fails(self):
        edits = (
            lambda a,b,p: a.update(status="FAIL"),
            lambda a,b,p: a["details"]["isolation"].update(
                network_isolation="UNPROVEN"),
            lambda a,b,p: b.update(errors=1),
            lambda a,b,p: b.update(methods_run=0),
            lambda a,b,p: p.update(reviewed_workflow_source_mode="active"),
            lambda a,b,p: p.update(historical_packaged_tooling_files_verified=34),
            lambda a,b,p: p.update(independent_security_review=True),
            lambda a,b,p: p.update(owner_activation_authorized=True),
            lambda a,b,p: p.update(changed_canonical_tooling=[]),
            lambda a,b,p: p["changed_canonical_tooling"][0].update(
                path="verification/archive/verify_bundle.py"),
        )
        for update in edits:
            old,now,profile=fixture()
            update(old,now,profile)
            with self.subTest(update=str(update)), self.assertRaises(
                    rehearsal.RehearsalError):
                rehearsal.validate_reports(old,now,profile,H)

    def test_two_real_child_command_shapes_and_unapproved_artifact(self):
        old,now,profile=fixture()
        with tempfile.TemporaryDirectory() as tmp:
            parent=Path(tmp)
            historical,current,out=parent/"T",parent/"H",parent/"out"
            historical.mkdir()
            (current/"archival/v0.2.0/supplement-1").mkdir(parents=True)
            ran=[]
            def exec_command(argv,cwd,**kwargs):
                ran.append((argv,cwd,kwargs))
                report=Path(argv[argv.index("--report")+1])
                report.write_text(json.dumps(old if kwargs.get(
                    "historical_artifact") else now))
                return SimpleNamespace(returncode=0,stdout="PASS",stderr="")
            with mock.patch.object(rehearsal.dual,"checkout",
                                   side_effect=[historical,current]), \
                 mock.patch.object(rehearsal,"tooling_audit",return_value=profile), \
                 mock.patch.object(rehearsal.dual,"command",
                                   side_effect=exec_command):
                result=rehearsal.execute(historical,current,H,out)
            self.assertEqual(len(ran),2)
            self.assertEqual((ran[0][1],ran[1][1]),(historical,current))
            self.assertTrue(ran[0][2]["historical_artifact"])
            self.assertTrue(ran[1][2]["detached_current_suite"])
            self.assertNotIn("--repo",ran[0][0])
            self.assertNotIn("--candidate",ran[0][0])
            self.assertEqual(result["status"],rehearsal.STATUS)
            data=json.loads((out/"STAGED_REHEARSAL_NOT_T2_AUTHORITY.json").read_bytes())
            self.assertFalse(data["original_T2_producer_zip"])
            self.assertTrue((out/"T_stdout.log").is_file())
            self.assertTrue((out/"current_H_workflow.json").is_file())


if __name__=="__main__":
    unittest.main()
