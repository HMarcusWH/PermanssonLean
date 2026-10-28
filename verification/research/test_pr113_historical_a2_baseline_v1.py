"""Real temporary-Git baseline tests; synthetic sources are never Lean evidence."""
from __future__ import annotations

import copy
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import pr113_historical_a2_baseline_v1 as baseline


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args],
                                   stderr=subprocess.DEVNULL, timeout=30).decode().strip()


def commit(root, message):
    git(root, "add", ".")
    git(root, "commit", "-qm", message)
    return git(root, "rev-parse", "HEAD")


class PositiveBaselineSourceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="positive-a2-baseline-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "repo"
        self.root.mkdir()
        git(self.root, "init", "-q")
        git(self.root, "config", "user.name", "Synthetic historical test")
        git(self.root, "config", "user.email", "synthetic@invalid.example")
        git(self.root, "config", "commit.gpgsign", "false")
        paths = (*baseline.EXECUTORS, baseline.ORIGINAL_TEST,
                 *baseline.PROOF_PATHS, *baseline.PIN_PATHS, "PermanssonResearch.lean")
        for path in paths:
            file = self.root / path
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_text("SYNTHETIC source, not a Lean proof: " + path + "\n")
        self.intro = commit(self.root, "synthetic introduction, not a positive result")
        proof = self.root / baseline.PROOF_PATHS[0]
        proof.write_text("SYNTHETIC corrected source, not a compiler receipt\n")
        self.positive = commit(self.root, "synthetic corrected baseline")
        self.tree = git(self.root, "rev-parse", "HEAD^{tree}")
        self.pins = {p: git(self.root, "rev-parse", "HEAD:" + p)
                     for p in baseline.EXECUTORS}
        self.test_pin = git(self.root, "rev-parse", "HEAD:" + baseline.ORIGINAL_TEST)
        patch = mock.patch.multiple(baseline, INTRODUCER=self.intro,
                                    REPLAY_HEAD=self.positive, REPLAY_TREE=self.tree,
                                    EXECUTORS=self.pins, ORIGINAL_TEST_BLOB=self.test_pin)
        patch.start()
        self.addCleanup(patch.stop)

    def test_corrected_source_is_distinct_and_does_not_claim_execution(self):
        result = baseline.verify_positive_source(self.root)
        self.assertNotEqual(result["introduction_sha"], result["positive_replay_sha"])
        self.assertEqual(result["positive_replay_tree"], self.tree)
        self.assertEqual(set(result["source_blobs"]), {
            *baseline.EXECUTORS, baseline.ORIGINAL_TEST, *baseline.PIN_PATHS,
            *baseline.PROOF_PATHS, "PermanssonResearch.lean"})
        for flag in ("fresh_compiler_execution", "independent_security_review", "mathematical_acceptance"):
            self.assertIs(result[flag], False)

    def test_introducer_cannot_be_used_as_positive_replay(self):
        git(self.root, "checkout", "--detach", self.intro)
        with self.assertRaisesRegex(baseline.HistoricalBaselineError, "corrected PR80"):
            baseline.verify_positive_source(self.root)

    def test_forged_tree_fails_before_execution(self):
        with mock.patch.object(baseline, "REPLAY_TREE", "0" * 40):
            with self.assertRaisesRegex(baseline.HistoricalBaselineError, "tree differs"):
                baseline.verify_positive_source(self.root)

    def test_wrong_executable_or_original_test_pin_is_rejected(self):
        for member in self.pins:
            with self.subTest(member=member), mock.patch.dict(baseline.EXECUTORS, {member: "0" * 40}):
                with self.assertRaisesRegex(baseline.HistoricalBaselineError, "executor/test changed"):
                    baseline.verify_positive_source(self.root)
        with mock.patch.object(baseline, "ORIGINAL_TEST_BLOB", "0" * 40):
            with self.assertRaises(baseline.HistoricalBaselineError):
                baseline.verify_positive_source(self.root)

    def test_dirty_source_is_rejected(self):
        (self.root / baseline.PROOF_PATHS[0]).write_text("uncommitted replacement\n")
        with self.assertRaisesRegex(baseline.HistoricalBaselineError, "dirty"):
            baseline.verify_positive_source(self.root)

    def test_assume_unchanged_cannot_hide_replaced_proof_bytes(self):
        member = baseline.PROOF_PATHS[0]
        git(self.root, "update-index", "--assume-unchanged", member)
        (self.root / member).write_text("untracked-by-index corruption\n")
        self.assertEqual(git(self.root, "status", "--porcelain=v1"), "")
        with self.assertRaisesRegex(baseline.HistoricalBaselineError, "bytes differ"):
            baseline.verify_positive_source(self.root)

    def test_source_directory_alias_is_rejected(self):
        alias = self.root.parent / "alias"
        alias.symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(baseline.HistoricalBaselineError, "symlinks"):
            baseline.verify_positive_source(alias)


class HistoricalDiagnosticTests(unittest.TestCase):
    def successful(self):
        return {"format": "Permansson.A2P02.CompilerReceipt.v2",
                "status": "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING",
                "source": {"git_head": baseline.REPLAY_HEAD,
                           "git_head_tree": baseline.REPLAY_TREE},
                "source_unchanged": True}

    def test_successful_status_still_requires_exact_source(self):
        row = self.successful()
        baseline.require_runtime_success(0, row)
        baseline.verify_receipt_source(row)
        for field, value in (("git_head", baseline.INTRODUCER),
                             ("git_head_tree", "f" * 40)):
            bad = copy.deepcopy(row)
            bad["source"][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(
                    baseline.HistoricalBaselineError, "SOURCE_MISMATCH"):
                baseline.verify_receipt_source(bad)

    def test_compiler_failure_exposes_label_exit_log_and_original_reason(self):
        row = {"status": "FAIL_CLOSED", "reason": "Unknown identifier mul_le_mul_left'",
               "commands": [{"label": "research_build", "returncode": 1,
                             "log": "02_research_build.log"}]}
        with self.assertRaises(baseline.HistoricalBaselineError) as caught:
            baseline.require_runtime_success(2, row)
        for text in ("COMPILER_FAILED", "process_exit=2", "command=research_build",
                     "command_exit=1", "02_research_build.log", "Unknown identifier"):
            self.assertIn(text, str(caught.exception))
        self.assertNotIn("SOURCE_MISMATCH", str(caught.exception))

    def test_zero_exit_cannot_upgrade_a_failed_receipt(self):
        with self.assertRaisesRegex(baseline.HistoricalBaselineError, "COMPILER_FAILED"):
            baseline.require_runtime_success(0, {"status": "FAIL_CLOSED", "commands": None})

    def test_boolean_exit_is_not_a_real_success_code(self):
        with self.assertRaises(baseline.HistoricalBaselineError):
            baseline.require_runtime_success(False, self.successful())

    def test_expected_semantic_negative_is_not_misreported_as_failed_positive(self):
        row = {"status": "FAIL_CLOSED", "reason": "source changed after controls",
               "commands": [{"label": "wrong_reported_effect", "returncode": 1}]}
        with self.assertRaises(baseline.HistoricalBaselineError) as caught:
            baseline.require_runtime_success(2, row)
        self.assertIn("command=unknown", str(caught.exception))
        self.assertIn("source changed after controls", str(caught.exception))

    def test_unbounded_diagnostic_is_truncated_not_accepted(self):
        with self.assertRaises(baseline.HistoricalBaselineError) as caught:
            baseline.require_runtime_success(2, {"status": "FAIL_CLOSED", "reason": "x" * 20000})
        self.assertLess(len(str(caught.exception)), 6500)


if __name__ == "__main__":
    unittest.main()
