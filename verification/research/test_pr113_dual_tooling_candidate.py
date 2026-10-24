"""Dual T/H report regression tests; mocks NEVER simulate real archive approval."""
import copy
import unittest
from unittest import mock
from types import SimpleNamespace
import pr113_dual_tooling_candidate as dual

T=dual.T
H="a"*40

def fixture():
    historical={
        "format":"Permansson.Hardening.Check.v1",
        "context":{"source":"immutable-T"},
        "check":"archive-reproducibility",
        "status":"PASS",
        "details":{
            "acceptance_scope":"accepted_artifact_replay_only",
            "isolation":{"network_isolation":"ENFORCED",
                         "capabilities":"all_zero"},
        },
    }
    current={
        "format":"Permansson.Hardening.Tests.v1","schema_version":1,
        "status":"PASS","suite":"workflow",
        "execution_tracked_clean":True,
        "methods_run":9, "failures":0, "errors":0, "skips":0,
        "covered_requirements":["CI-06","CI-07"],
    }
    return historical,current

class DualToolingTests(unittest.TestCase):
    def test_historical_and_new_provenance_stays_unapproved(self):
        old,now=fixture()
        result=dual.validate_dual_reports(old,now,T_source=T,H_source=H)
        self.assertEqual(result["status"],"DUAL_T_AND_H_EXECUTED_UNREVIEWED")
        self.assertTrue(result["original_T_archive_offline_restoration_passed"])
        self.assertFalse(result["independent_security_review"])
        self.assertFalse(result["required_current_archive_CI_green"])
        self.assertFalse(result["mathematical_release_approved"])

    def test_missing_isolation_or_bypassed_historical_T_fails(self):
        for key,value in [("status","FAIL"),("details",{}),
                          ("check","wrong context")]:
            old,now=fixture()
            old[key]=value
            with self.subTest(key=key), self.assertRaises(dual.DualToolingError):
                dual.validate_dual_reports(old,now,T_source=T,H_source=H)
        for fault in ("network_isolation","capabilities"):
            old,now=fixture()
            old["details"]["isolation"][fault]="NOT_ENFORCED"
            with self.subTest(fault=fault), self.assertRaises(dual.DualToolingError):
                dual.validate_dual_reports(old,now,T_source=T,H_source=H)

    def test_tampered_run_or_missing_coverage_is_rejected(self):
        for field, changed in (
            ("format","Permansson.Hardening.Check.v0"),
            ("context",None),
        ):
            old,now=fixture()
            old[field]=changed
            with self.subTest(field=field), self.assertRaises(dual.DualToolingError):
                dual.validate_dual_reports(old,now,T_source=T,H_source=H)
        for field,changed in (
            ("covered_requirements",[]),("errors",1),("skips",1),
            ("failures",1),("schema_version",2),
        ):
            old,now=fixture()
            now[field]=changed
            with self.subTest(field=field), self.assertRaises(dual.DualToolingError):
                dual.validate_dual_reports(old,now,T_source=T,H_source=H)

    def test_real_branch_push_candidate_job_may_run_without_authorizing_archive(self):
        context = {
            "GITHUB_ACTIONS": "true",
            "GITHUB_REPOSITORY": "HMarcusWH/PermanssonLean",
            "GITHUB_SHA": H,
            "GITHUB_REF": "refs/heads/research/final-mathematical-closure",
            "GITHUB_EVENT_NAME": "push",
            "GITHUB_JOB": "original-T-and-current-H",
            "GITHUB_WORKFLOW": "PR113 Historical T and A2 candidates",
        }
        with mock.patch.dict(dual.os.environ, context, clear=True):
            self.assertEqual(
                dual.candidate_ci_context(H),
                "REVIEWED_SOURCE_PUSH_CANDIDATE_UNAPPROVED")
            for key, value in (
                ("GITHUB_SHA", "b" * 40),
                ("GITHUB_REF", "refs/heads/main"),
                ("GITHUB_EVENT_NAME", "workflow_dispatch"),
                ("GITHUB_JOB", "archive-reproducibility"),
                ("GITHUB_WORKFLOW", "Research integrity"),
                ("GITHUB_REPOSITORY", "someone/else"),
            ):
                with self.subTest(key=key):
                    with mock.patch.dict(dual.os.environ, {key: value}):
                        with self.assertRaises(dual.DualToolingError):
                            dual.candidate_ci_context(H)

    def test_local_invocation_remains_unapproved(self):
        with mock.patch.dict(dual.os.environ,
                             {"GITHUB_ACTIONS": ""}, clear=True):
            self.assertEqual(dual.candidate_ci_context(H),
                             "LOCAL_UNREVIEWED")

    def test_historical_original_process_has_no_ci_or_secret_inheritance(self):
        context = {
            "GITHUB_ACTIONS": "true",
            "GITHUB_SHA": H,
            "GITHUB_TOKEN": "not-for-historical-T",
            "GH_TOKEN": "not-for-historical-T",
            "GIT_CONFIG_GLOBAL": "test",
            "CI": "true",
            "CLOUD_SECRET": "test",
            "HTTPS_PROXY": "http://proxy.invalid",
            "PYTHONPATH": "forbidden_current_H_import",
            "PATH": "/usr/bin",
        }
        fake = SimpleNamespace(returncode=0, stdout="PASS", stderr="")
        with mock.patch.dict(dual.os.environ, context, clear=True):
            with mock.patch.object(dual.subprocess, "run", return_value=fake) as run:
                dual.command(["python", "-B", "-m",
                              "verification.archive.offline_smoke"], "/tmp/T",
                             historical_artifact=True)
                environment = run.call_args.kwargs["env"]
        self.assertNotIn("GITHUB_ACTIONS", environment)
        self.assertNotIn("GITHUB_SHA", environment)
        self.assertNotIn("GITHUB_TOKEN", environment)
        self.assertNotIn("GH_TOKEN", environment)
        self.assertNotIn("GIT_CONFIG_GLOBAL", environment)
        self.assertNotIn("CI", environment)
        self.assertNotIn("CLOUD_SECRET", environment)
        self.assertNotIn("HTTPS_PROXY", environment)
        self.assertNotIn("PYTHONPATH", environment)
        self.assertEqual(environment["PYTHONDONTWRITEBYTECODE"], "1")
        self.assertEqual(environment["PATH"], "/usr/bin")

    def test_current_H_verifier_does_not_borrow_standalone_T_environment(self):
        context = {"GITHUB_ACTIONS": "true", "GITHUB_SHA": H,
                   "GITHUB_EVENT_NAME": "push",
                   "PYTHONPATH": "untrusted-import"}
        fake = SimpleNamespace(returncode=0, stdout="PASS", stderr="")
        with mock.patch.dict(dual.os.environ, context, clear=True):
            with mock.patch.object(dual.subprocess, "run", return_value=fake) as run:
                dual.command(["python", "-B", "-m",
                              "verification.integrity.run_tests"], "/tmp/H")
                environment = run.call_args.kwargs["env"]
        self.assertEqual(environment["GITHUB_ACTIONS"], "true")
        self.assertEqual(environment["GITHUB_SHA"], H)
        self.assertNotIn("PYTHONPATH", environment)

    def test_failed_historical_T_subprocess_stays_red_not_approved(self):
        fake = SimpleNamespace(returncode=3, stdout="historical: BLOCKED",
                               stderr="E_OFFLINE_UNAVAILABLE")
        with mock.patch.object(dual.subprocess, "run", return_value=fake):
            with self.assertRaisesRegex(dual.DualToolingError, "exited 3"):
                dual.command(["python", "-m", "verification.archive.offline_smoke"],
                             "/tmp/T", historical_artifact=True)

    def test_unexecuted_current_workflow_or_dirty_source_rejected(self):
        for key,value in [("status","FAIL"),
                          ("suite","reference"),
                          ("execution_tracked_clean",False),
                          ("methods_run",0)]:
            old,now=fixture()
            now[key]=value
            with self.subTest(key=key), self.assertRaises(dual.DualToolingError):
                dual.validate_dual_reports(old,now,T_source=T,H_source=H)
