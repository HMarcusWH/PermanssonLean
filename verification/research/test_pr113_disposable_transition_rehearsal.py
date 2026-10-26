"""Actual disposable Git worktree/source rehearsal; no protected activation.

One test runs the complete staged 25->30 installation using disposable Git
objects and proves genuine ordered synthetic S source identity. The original
PR branch, workflow files, owner/reviewer state and release claims stay inert.
"""
import json
from pathlib import Path
import tempfile
import unittest

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
                             "SEVEN_REAL_ACTIVE30_SUITES_PASSED_UNREVIEWED")
            self.assertEqual(len(regression["executed_suites"]),7)
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

    def test_foreign_or_nonexistent_head_never_creates_temporary_checkout(self):
        with tempfile.TemporaryDirectory(prefix="pr113-report-outside-") as temp:
            report=Path(temp)/"never_created.json"
            for requested in ("wrong", "0"*40):
                with self.subTest(head=requested),self.assertRaises(
                        (ValueError,RuntimeError)):
                    rehearsal.execute(requested,report)
                self.assertFalse(report.exists())
