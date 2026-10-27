"""Actual disposable Git worktree/source rehearsal; no protected activation.

One test runs the complete staged 25->30 installation using disposable Git
objects and proves genuine ordered synthetic S source identity. The original
PR branch, workflow files, owner/reviewer state and release claims stay inert.
"""
import json
import subprocess
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import pr113_disposable_transition_rehearsal as rehearsal

ROOT=Path(__file__).resolve().parents[2]


class RealDisposableRehearsalTests(unittest.TestCase):
    def test_exact_current_source_25_to_30_in_detached_git_worktree(self):
        source=rehearsal.scalar(ROOT,"rev-parse","HEAD")
        parents=rehearsal.scalar(
            ROOT,"show","-s","--format=%P",source).split()
        head=(parents[1] if len(parents)==2
              and parents[0]==rehearsal.PR113_BASE else source)
        phase,pre=rehearsal.audited_source_phase(ROOT,source)
        self.assertIn(phase,("staged","active"))
        self.assertEqual(pre["historical_original_workflow_count"],25)
        before=rehearsal.scalar(ROOT,"rev-parse","HEAD")
        with tempfile.TemporaryDirectory(prefix="pr113-report-outside-") as temp:
            report_path=Path(temp)/"source_rehearsal.json"
            result=rehearsal.execute(head,report_path)
            self.assertEqual(result["status"],
                ("DISPOSABLE_SOURCE_AND_ORDERED_SYNTHETIC_REHEARSED_UNREVIEWED"
                 if phase=="staged" else
                 "DISPOSABLE_ACTIVE_30_AND_ORDERED_SYNTHETIC_REHEARSED_UNREVIEWED"))
            self.assertEqual(result["source_phase_at_invocation"],phase)
            workflow=result["current30_CI06_CI07_workflow_suite"]
            self.assertEqual(workflow["status"],
                "CURRENT_30_WORKFLOW_CI06_CI07_EXECUTED_LOCALLY")
            self.assertEqual(workflow["covered_requirements"],
                             ["CI-06","CI-07"])
            self.assertGreaterEqual(workflow["methods_run"],8)
            self.assertTrue(workflow["real_execution"])
            self.assertFalse(workflow["required_github_check_authenticated"])
            self.assertFalse(result["current30_local_suite_is_required_CI"])
            regression=result["current30_phase_aware_regressions"]
            self.assertEqual(regression["status"],
                             "EIGHT_REAL_ACTIVE30_SUITES_PASSED_UNREVIEWED")
            self.assertEqual(len(regression["executed_suites"]),8)
            self.assertEqual(regression["checked_sha"],
                             result["disposable_current_source_commit"])
            self.assertTrue(all(x["status"]=="PASS_EXECUTED"
                                for x in regression["executed_suites"]))
            self.assertEqual({x["source_test"]
                              for x in regression["executed_suites"]},
                             set(rehearsal.ACTIVE_30_SUITES))
            self.assertFalse(regression["required_github_ci_authenticated"])
            self.assertFalse(regression["independent_security_review"])
            self.assertEqual(workflow["source_head"],
                             result["disposable_current_source_commit"])
            self.assertEqual(result["historical_original_workflow_count"],25)
            self.assertEqual(result["current_reviewed_workflow_count"],30)
            self.assertEqual(result["retained_workflow_count"],23)
            self.assertEqual(result["replacement_workflow_count"],2)
            self.assertEqual(result["addition_workflow_count"],5)
            self.assertEqual(result["actual_requested_head"],head)
            self.assertEqual(result["source_at_invocation"],source)
            if phase=="staged":
                self.assertNotEqual(result["disposable_current_source_commit"],head)
            else:
                self.assertEqual(result["disposable_current_source_commit"],head)
            self.assertNotEqual(result["disposable_synthetic_source_commit"],
                                result["disposable_current_source_commit"])
            self.assertEqual(result["profile_sha256"],
                             result["synthetic_profile_sha256"])
            self.assertTrue(result["disposable_source_mutation_rejected"])
            for field in (
                "source_bound_GitHub_producer_authenticated",
                "independent_security_review","owner_activation_authorized",
                "all_required_CI_green","mathematical_acceptance",
                "owner_merge_authorized","publication_authorized",
            ):
                self.assertIs(result[field],False,field)
            self.assertEqual(result["original_T_archive_replay"],"NOT_EXECUTED")
            self.assertEqual(result["original_A2_compiler_replay"],"NOT_EXECUTED")
            self.assertEqual(json.loads(report_path.read_bytes()),result)
            # Persist the exact detached C/S source receipt in the genuine
            # GitHub research job log before the scratch directory is removed.
            # This does not fabricate a CI/security/release approval.
            print("\nPR113_R5_SOURCE_REHEARSAL_RECEIPT_BEGIN")
            print(json.dumps(result,sort_keys=True))
            print("PR113_R5_SOURCE_REHEARSAL_RECEIPT_END")
        self.assertEqual(before,rehearsal.scalar(ROOT,"rev-parse","HEAD"))
        self.assertFalse(rehearsal.run(
            ROOT,"status","--porcelain=v1","--untracked-files=all"))

    def test_nested_failure_retains_exact_method_and_exit_status(self):
        """A failed nested test must stay red and identify the failing method."""
        name=("verification.integrity.tests.test_workflow.WorkflowTests."
              "test_shell_background_and_redirection_rejected")
        with tempfile.TemporaryDirectory(prefix="pr113-nested-fail-test-") as temp:
            checkout=Path(temp)/"source"
            checkout.mkdir()
            evidence=Path(temp)/"workflow-tests.json"
            def failed_child(command,**kwargs):
                self.assertEqual(command[-1],str(evidence))
                evidence.write_text(json.dumps({
                    "format":"Permansson.Hardening.Tests.v1",
                    "suite":"workflow",
                    "status":"FAIL",
                    "error_code":"E_REPORT",
                    "message":"Suite failed, skipped, or incomplete",
                    "methods_run":8,
                    "failures":1,
                    "errors":0,
                    "skips":0,
                    "results":[{"method":name,"status":"FAIL"}],
                }),encoding="utf-8")
                return subprocess.CompletedProcess(
                    command,1,"workflow: FAIL\n",
                    "FAIL: "+name+"\nAssertionError: expected E_WORKFLOW_CONTRACT\n")
            with mock.patch.object(rehearsal,"scalar",return_value="a"*40), \
                    mock.patch.object(rehearsal.subprocess,"run",
                                      side_effect=failed_child):
                with self.assertRaises(rehearsal.RehearsalError) as raised:
                    rehearsal.run_installed_workflow_suite(checkout,evidence)
            message=str(raised.exception)
            self.assertIn(name,message)
            self.assertIn("E_REPORT",message)
            self.assertIn('"nested_returncode": 1',message)
            self.assertIn('"status": "FAIL_CLOSED"',message)
            self.assertEqual(json.loads(evidence.read_text())["status"],"FAIL")

    def test_active_30_rehearsal_requires_both_legacy_import_consumers(self):
        actual=rehearsal.ACTIVE_30_SUITES
        self.assertEqual(len(actual),8)
        self.assertEqual(len(set(actual)),8)
        self.assertIn("test_pr113_successor_workflow_profile.py",actual)
        self.assertIn("test_pr113_atomic_migration_preview.py",actual)
        self.assertIn("test_pr113_tooling_migration_v2.py",actual)
        self.assertIn("test_pr113_a2_successor_identity_v2.py",actual)

    def test_foreign_or_nonexistent_head_never_creates_temporary_checkout(self):
        with tempfile.TemporaryDirectory(prefix="pr113-report-outside-") as temp:
            report=Path(temp)/"never_created.json"
            for requested in ("wrong", "0"*40):
                with self.subTest(head=requested),self.assertRaises(
                        (ValueError,RuntimeError)):
                    rehearsal.execute(requested,report)
                self.assertFalse(report.exists())
