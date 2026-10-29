"""Actual disposable Git worktree/source rehearsal; no protected activation.

One test runs the complete staged 25->30 installation using disposable Git
objects and proves genuine ordered synthetic S source identity. The original
PR branch, workflow files, owner/reviewer state and release claims stay inert.
"""
import io
import json
import subprocess
from contextlib import redirect_stderr
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
            # Keep synthetic failure markers out of successful real CI logs.
            # Assert the actual failure renderer emits them when required.
            captured=io.StringIO()
            with redirect_stderr(captured):
                with mock.patch.object(rehearsal,"scalar",return_value="a"*40), \
                        mock.patch.object(rehearsal.subprocess,"run",
                                          side_effect=failed_child):
                    with self.assertRaises(rehearsal.RehearsalError) as raised:
                        rehearsal.run_installed_workflow_suite(checkout,evidence)
            self.assertIn("PR113_NESTED_WORKFLOW_FAILURE_BEGIN",
                          captured.getvalue())
            self.assertIn(name,captured.getvalue())
            message=str(raised.exception)
            self.assertIn(name,message)
            self.assertIn("E_REPORT",message)
            self.assertIn('"nested_returncode": 1',message)
            self.assertIn('"status": "FAIL_CLOSED"',message)
            self.assertEqual(json.loads(evidence.read_text())["status"],"FAIL")

    def test_active30_regression_failure_retains_exact_method_and_error(self):
        """Synthetic red subprocess exercises real receipt and fail-closed code."""
        first=rehearsal.ACTIVE_30_SUITES[0]
        qualified=("test_pr113_tooling_migration_v2."
                   "ToolingMigrationTests.test_reject_changed_archive_blob")
        stderr=(
            "test_reject_changed_archive_blob ("+qualified+") ... FAIL\n"
            + "harmless preceding diagnostics\n"*500
            + "======================================================================\n"
            + "FAIL: test_reject_changed_archive_blob ("+qualified+")\n"
            + "----------------------------------------------------------------------\n"
            + "Traceback (most recent call last):\n"
            + "AssertionError: wrong pinned source remains unverified\n"
            + "----------------------------------------------------------------------\n"
            + "Ran 3 tests in 0.012s\n\nFAILED (failures=1)\n"
        )
        failed=subprocess.CompletedProcess(["python"],1,"",stderr)
        with tempfile.TemporaryDirectory(prefix="pr113-active30-negative-") as tmp:
            checkout=Path(tmp)/"repo"
            source=checkout/"verification/research"/first
            source.parent.mkdir(parents=True)
            source.write_text("# isolated test fixture\n",encoding="utf-8")
            outside=Path(tmp)/"detached-logs"
            capture=io.StringIO()
            with mock.patch.object(rehearsal.subprocess,"run",return_value=failed), \
                    mock.patch.object(rehearsal,"scalar",return_value="a"*40), \
                    redirect_stderr(capture):
                with self.assertRaises(rehearsal.RehearsalError) as caught:
                    rehearsal.run_active_30_regressions(checkout,outside)
            report=json.loads((outside/"FAILURE_ONLY.json").read_bytes())
            self.assertEqual(report["status"],"FAIL_CLOSED")
            self.assertEqual(report["failed_suite"],first)
            self.assertEqual(report["failed_returncode"],1)
            self.assertEqual(report["tests_run"],3)
            self.assertEqual(report["failed_methods"][0]["method"],qualified)
            self.assertIn("wrong pinned source",report["error_summaries"][0])
            self.assertEqual(report["diagnostic_tail"][-40:],
                             stderr.rstrip()[-40:])
            self.assertIn("PR113_ACTIVE30_FAILURE_RECEIPT_BEGIN",
                          capture.getvalue())
            self.assertIn(qualified,str(caught.exception))
            self.assertFalse(report["independent_security_review"])
            self.assertFalse(report["github_required_ci_authenticated"])

    def test_active30_zero_skipped_forged_ok_and_error_stay_red(self):
        """Only genuine nonempty unittest OK is a passing subprocess."""
        make=subprocess.CompletedProcess
        examples=(
            make(["python"],0,"","Ran 0 tests in 0.001s\n\nOK\n"),
            make(["python"],0,"","Ran 2 tests in 0.001s\n\nOK (skipped=1)\n"),
            make(["python"],0,"","OK\n"),
            make(["python"],1,"","ERROR: testcase (module.Case.testcase)\n"
                                  "RuntimeError: fixture failed\n"),
            make(["python"],0,"","Ran 2 tests in 0.001s\n\nFAILED (errors=1)\n"),
        )
        for process in examples:
            with self.subTest(output=process.stderr):
                self.assertFalse(rehearsal._active30_suite_passed(
                    process,process.stdout+"\n"+process.stderr))
        positive=make(["python"],0,"","Ran 2 tests in 0.001s\n\nOK\n")
        self.assertTrue(rehearsal._active30_suite_passed(
            positive,positive.stdout+"\n"+positive.stderr))
        with tempfile.TemporaryDirectory(prefix="pr113-active30-redact-") as tmp:
            checkout=Path(tmp)
            with mock.patch.object(rehearsal,"scalar",return_value="b"*40):
                report=rehearsal._active30_failure_receipt(
                    checkout,"synthetic.py",examples[3],
                    "ERROR: testcase (module.Case.testcase)\n"
                    "ValueError: incorrect assumption\n"
                    "GITHUB_TOKEN: example-synthetic-secret\n",
                    [],timed_out=False)
            self.assertEqual(report["failed_methods"][0]["method"],
                             "module.Case.testcase")
            self.assertIn("[redacted credential-bearing diagnostic line]",
                          report["diagnostic_head"])
            self.assertNotIn("example-synthetic-secret",
                             json.dumps(report))

    def test_active30_timeout_is_red_and_source_receipt_not_approval(self):
        first=rehearsal.ACTIVE_30_SUITES[0]
        with tempfile.TemporaryDirectory(prefix="pr113-active30-timeout-") as tmp:
            checkout=Path(tmp)/"repo"
            test_source=checkout/"verification/research"/first
            test_source.parent.mkdir(parents=True)
            test_source.write_text("# synthetic runner fixture\n",encoding="utf-8")
            outside=Path(tmp)/"detached"
            timeout=subprocess.TimeoutExpired(["python"],150,
                                              output=b"test_started\n")
            capture=io.StringIO()
            with mock.patch.object(rehearsal.subprocess,"run",side_effect=timeout), \
                    mock.patch.object(rehearsal,"scalar",return_value="c"*40), \
                    redirect_stderr(capture):
                with self.assertRaises(rehearsal.RehearsalError):
                    rehearsal.run_active_30_regressions(checkout,outside)
            report=json.loads((outside/"FAILURE_ONLY.json").read_bytes())
            self.assertTrue(report["timed_out"])
            self.assertEqual(report["failed_returncode"],124)
            self.assertEqual(report["status"],"FAIL_CLOSED")
            self.assertIn("ACTIVE30_SUBPROCESS_TIMEOUT",capture.getvalue())

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
