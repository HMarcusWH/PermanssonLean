"""Real subprocess/ZIP boundary tests; archive executors are SYNTHETIC.

No temporary fixture is an isolated historical restoration, a GitHub producer
artifact, a reviewer decision or permission to activate a protected workflow.
"""
from __future__ import annotations

import copy
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
import zipfile

import pr113_t2_execution_io_v1 as boundary
import pr113_dual_tooling_candidate_v2 as dual
import pr113_archive_pre_activation_rehearsal_v1 as rehearsal
from infrastructure_acceptance import inspect_zip, InfrastructureError
from test_pr113_archive_pre_activation_rehearsal_v1 import fixture, H


def archive(root):
    stream = io.BytesIO()
    with zipfile.ZipFile(stream, "w", zipfile.ZIP_DEFLATED) as output:
        for path in root.iterdir():
            output.write(path, path.name)
    return stream.getvalue()


class RetainedChildTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="t2-child-tests-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.out = self.root / "evidence"
        self.out.mkdir()

    def run_child(self, code, **kwargs):
        return boundary.execute_logged(
            [sys.executable, "-B", "-c", code], self.root, os.environ.copy(),
            self.out, "T", **kwargs)

    def receipt(self):
        return json.loads((self.out / "T.execution.json").read_bytes())

    def test_zero_exit_with_empty_streams_is_non_authorizing_and_zip_safe(self):
        completed = self.run_child("pass")
        self.assertEqual(completed.returncode, 0)
        report = self.receipt()
        self.assertEqual(report["status"], "CHILD_EXIT_ZERO_REPORTS_UNVERIFIED")
        self.assertFalse(report["independent_security_review"])
        self.assertFalse(report["required_ci_accepted"])
        self.assertFalse(report["merge_authorized"])
        for stream in ("stdout", "stderr"):
            self.assertIsNone(report["logs"][stream]["file"])
            self.assertEqual(report["logs"][stream]["sha256"],
                             hashlib.sha256(b"").hexdigest())
        self.assertEqual(boundary.evidence_files(self.out), ["T.execution.json"])
        self.assertEqual(set(inspect_zip(archive(self.out))), {"T.execution.json"})

    def test_real_nonzero_child_retains_both_logs_before_raising(self):
        with self.assertRaisesRegex(boundary.EvidenceExecutionError, "NONZERO_EXIT"):
            self.run_child("import sys; print('synthetic stdout'); "
                           "print('synthetic failure',file=sys.stderr); sys.exit(7)")
        report = self.receipt()
        self.assertEqual(report["returncode"], 7)
        self.assertEqual(report["failure_kind"], "NONZERO_EXIT")
        for row in report["logs"].values():
            raw = (self.out / row["file"]).read_bytes()
            self.assertEqual(hashlib.sha256(raw).hexdigest(), row["sha256"])
            self.assertEqual(len(raw), row["bytes"])
        self.assertEqual(len(inspect_zip(archive(self.out))), 3)

    def test_real_timeout_retains_diagnostics_without_green_result(self):
        with self.assertRaisesRegex(boundary.EvidenceExecutionError, "TIMEOUT"):
            self.run_child("import time; print('before timeout',flush=True); "
                           "time.sleep(10)", timeout=0.5)
        report = self.receipt()
        self.assertEqual(report["failure_kind"], "TIMEOUT")
        self.assertNotEqual(report["returncode"], 0)
        # A loaded runner may time out before Python prints anything. Even
        # then the nonempty failure sidecar must survive and be ZIP-safe.
        files = inspect_zip(archive(self.out))
        self.assertIn("T.execution.json", files)
        if report["logs"]["stdout"]["file"] is not None:
            self.assertIn(b"before timeout", files["T.stdout.log"])

    def test_log_budget_overflow_is_rejected_and_saved_bytes_are_bounded(self):
        with self.assertRaisesRegex(boundary.EvidenceExecutionError, "LOG_BUDGET"):
            self.run_child("print('x' * 10000)", max_log_bytes=128)
        report = self.receipt()
        self.assertTrue(report["logs"]["stdout"]["truncated"])
        self.assertEqual((self.out / "T.stdout.log").stat().st_size, 128)
        self.assertEqual(report["failure_kind"], "LOG_BUDGET_EXCEEDED")

    def test_missing_executable_retains_nonempty_failure_sidecar(self):
        with self.assertRaisesRegex(boundary.EvidenceExecutionError, "LAUNCH_ERROR"):
            boundary.execute_logged([str(self.root / "absent")], self.root,
                                    os.environ.copy(), self.out, "T")
        self.assertIsNone(self.receipt()["returncode"])
        self.assertTrue((self.out / "T.stderr.log").stat().st_size)
        self.assertEqual(len(inspect_zip(archive(self.out))), 2)

    def test_existing_evidence_is_never_overwritten(self):
        marker = self.out / "T.execution.json"
        marker.write_bytes(b"original bytes")
        with self.assertRaisesRegex(boundary.EvidenceExecutionError, "overwritten"):
            self.run_child("pass")
        self.assertEqual(marker.read_bytes(), b"original bytes")

    def test_symlinked_output_and_log_are_rejected(self):
        alias = self.root / "alias"
        alias.symlink_to(self.out, target_is_directory=True)
        with self.assertRaises(boundary.EvidenceExecutionError):
            boundary.execute_logged([sys.executable, "-c", "pass"], self.root,
                                    os.environ.copy(), alias, "T")
        (self.out / "T.stderr.log").symlink_to(self.root / "missing")
        with self.assertRaises(boundary.EvidenceExecutionError):
            self.run_child("pass")

    def test_unbounded_or_traversing_command_inputs_rejected(self):
        for options in ({"timeout": float("inf")}, {"timeout": float("nan")},
                        {"timeout": True}, {"max_log_bytes": True},
                        {"max_log_bytes": 0}):
            with self.subTest(options=options), self.assertRaises(
                    boundary.EvidenceExecutionError):
                self.run_child("pass", **options)
        with self.assertRaises(boundary.EvidenceExecutionError):
            boundary.execute_logged([sys.executable, "-c", "pass"], self.root,
                                    os.environ.copy(), self.out, "../outside")
        self.assertEqual(list(self.out.iterdir()), [])

    def test_directory_and_empty_member_rejected_by_both_producer_and_consumer(self):
        for directory in (False, True):
            item = self.out / "restore-scratch"
            item.mkdir() if directory else item.write_bytes(b"")
            with self.subTest(directory=directory):
                with self.assertRaises(boundary.EvidenceExecutionError):
                    boundary.evidence_files(self.out)
                with self.assertRaises(InfrastructureError):
                    inspect_zip(archive(self.out))
            item.rmdir() if directory else item.unlink()

    def test_case_collisions_and_missing_required_report_rejected(self):
        (self.out / "report.json").write_text("{}")
        with self.assertRaises(boundary.EvidenceExecutionError):
            boundary.evidence_files(self.out, required=("other.json",))
        (self.out / "REPORT.JSON").write_text("{}")
        with self.assertRaises(boundary.EvidenceExecutionError):
            boundary.evidence_files(self.out)

    def test_report_boundary_rejects_duplicate_nonfinite_and_symlink(self):
        target = self.out / "report.json"
        for raw in (b'{"status":"FAIL","status":"PASS"}', b'{"x":NaN}',
                    b'[]', b''):
            target.write_bytes(raw)
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                boundary.read_report(target)
        target.write_text('{"status":"SYNTHETIC"}')
        self.assertEqual(boundary.read_report(target)["status"], "SYNTHETIC")
        alias = self.out / "alias.json"
        alias.symlink_to(target)
        with self.assertRaises(ValueError):
            boundary.read_report(alias)


class DualRunnerScratchTests(unittest.TestCase):
    """Synthetic reports, but actual subprocesses, logs, ZIP reader and cleanup."""
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="t2-runner-tests-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.old, self.current = self.root / "T", self.root / "H"
        self.out = self.root / "evidence"
        old, new, self.profile = fixture()
        self.profile["original_release_base_B"] = "b" * 40
        self.scratch_record = self.root / "scratch-location"
        self.h_called = self.root / "current-called"
        # These fixture modules impersonate no real historical execution.
        for root, module, report in (
                (self.old, "verification/archive/offline_smoke.py", old),
                (self.current, "verification/integrity/run_tests.py", new)):
            source = root / module
            source.parent.mkdir(parents=True)
            for parent in (source.parent, root / "verification"):
                (parent / "__init__.py").write_text("")
            source.write_text(
                "import json,os,pathlib,sys\n"
                "args=sys.argv[1:]\n"
                "assert 'GITHUB_TOKEN' not in os.environ\n"
                "assert 'GITHUB_ACTIONS' not in os.environ\n"
                "assert 'PYTHONPATH' not in os.environ\n"
                "if '--scratch' in args:\n"
                " p=pathlib.Path(args[args.index('--scratch')+1]); p.mkdir()\n"
                " (p/'.git').mkdir()\n"
                " for i in range(510): (p/str(i)).write_text('')\n"
                f" pathlib.Path({str(self.scratch_record)!r}).write_text(str(p))\n"
                "else:\n"
                f" pathlib.Path({str(self.h_called)!r}).write_text('SYNTHETIC')\n"
                "pathlib.Path(args[args.index('--report')+1]).write_text(\n"
                f" json.dumps({report!r}))\n"
                "print('SYNTHETIC archive-test child, not original evidence')\n")
        (self.current / "archival/v0.2.0/supplement-1").mkdir(parents=True)

    def execute(self, staged=False, profile_drift=False):
        target = rehearsal if staged else dual
        profile = copy.deepcopy(self.profile)
        profile["reviewed_workflow_source_mode"] = "staged" if staged else "active"
        after = copy.deepcopy(profile)
        if profile_drift:
            after["workflow_profile_sha256"] = "0" * 64
        with mock.patch.object(dual, "checkout", side_effect=[
                self.old, self.current, self.old, self.current]) as checked, \
             mock.patch.object(target, "tooling_audit", side_effect=[profile, after]), \
             mock.patch.object(dual, "candidate_ci_context", return_value="LOCAL_UNREVIEWED"), \
             mock.patch.dict(os.environ, {"GITHUB_TOKEN": "SYNTHETIC_DO_NOT_FORWARD",
                                         "GITHUB_ACTIONS": "true", "PYTHONPATH": "invalid"}):
            result = target.execute(self.old, self.current, H, self.out)
        self.assertEqual(checked.call_count, 4)
        return result

    def test_active_output_contains_only_direct_consumer_compatible_evidence(self):
        receipt = self.execute()
        self.assertEqual(receipt["status"], "DUAL_T_AND_30_H_EXECUTED_UNREVIEWED")
        self.assertFalse(receipt["independent_security_review"])
        self.assertFalse(receipt["required_current_archive_CI_green"])
        files = inspect_zip(archive(self.out))
        self.assertEqual(len(files), 8)
        self.assertTrue(self.h_called.exists())
        scratch = Path(self.scratch_record.read_text())
        self.assertFalse(scratch.is_relative_to(self.out))
        self.assertFalse(scratch.exists())
        self.assertFalse(scratch.parent.exists())

    def test_staged_output_never_claims_active30_or_required_CI(self):
        receipt = self.execute(staged=True)
        self.assertFalse(receipt["active_30_reverified"])
        self.assertFalse(receipt["genuine_required_ci"])
        self.assertFalse(receipt["original_T2_producer_zip"])
        self.assertIn("STAGED_REHEARSAL_NOT_T2_AUTHORITY.json",
                      inspect_zip(archive(self.out)))
        self.assertFalse(Path(self.scratch_record.read_text()).exists())
        self.assertFalse((self.out / "T_stderr.log").exists())

    def test_failed_original_child_keeps_logs_and_cleans_restore_scratch(self):
        source = self.old / "verification/archive/offline_smoke.py"
        source.write_text(source.read_text() + "sys.exit(7)\n")
        with self.assertRaisesRegex(dual.DualToolingError, "NONZERO_EXIT"):
            self.execute()
        self.assertFalse(self.h_called.exists())
        self.assertFalse(Path(self.scratch_record.read_text()).exists())
        self.assertEqual(json.loads((self.out / "T.execution.json").read_bytes())[
            "returncode"], 7)
        self.assertFalse((self.out / "dual_tooling_unreviewed.json").exists())
        self.assertIn("T.stdout.log", inspect_zip(archive(self.out)))

    def test_changed_source_profile_cannot_emit_success_receipt(self):
        with self.assertRaisesRegex(dual.DualToolingError, "profile changed"):
            self.execute(profile_drift=True)
        self.assertFalse((self.out / "dual_tooling_unreviewed.json").exists())
        self.assertFalse(Path(self.scratch_record.read_text()).exists())


if __name__ == "__main__":
    unittest.main()
