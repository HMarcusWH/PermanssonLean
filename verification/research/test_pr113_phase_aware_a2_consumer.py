"""Synthetic four-phase regression for the staged A2 required consumer.

This tests the *real* check_stored validator and mocks only its external
GitHub producer/review recomputation. No fixture is an actual approval.
"""
from __future__ import annotations

from contextlib import redirect_stdout
import importlib.util
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import pr113_historical_runtime_v3 as runtime

ROOT = Path(__file__).resolve().parents[2]
STAGED = ROOT / (
    "docs/operations/pr113_required_gate_replacement_unapproved/"
    "test_localized_prefix_compiler.py")
SPEC = importlib.util.spec_from_file_location(
    "pr113_staged_phase_aware_a2_consumer", STAGED)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("staged A2 consumer source absent")
consumer = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(consumer)

H = "b" * 40
M = "c" * 40
C = "d" * 40
PHASES = (
    "initial_113_pr", "initial_113_main",
    "main_descendant_pr", "main_descendant_push",
)


def event(phase):
    return {
        "phase": phase, "source_commit_sha": C,
        "github_run_id": 222, "github_run_attempt": 1,
        "base_sha": "17c315f7df7abf457eb94d393bd526d46da6f6f4",
        "head_sha": H, "synthetic_sha": C,
        "infrastructure_head_sha": H,
        "infrastructure_merge_sha": M if phase != "initial_113_pr" else None,
    }


def fabricated_result(phase):
    observed = event(phase)
    status = consumer.PHASE_STATUSES[phase]
    source = {"status": status}
    if phase.startswith("initial_113"):
        source.update({
            "independent_security_review_authenticated": True,
            "head_sha": H, "required_ci_successful": 0,
            "mathematical_acceptance": False,
            "owner_merge_authorized": False,
            "publication_authorized": False,
        })
        return {
            "phase": phase, "event": observed, "required": source,
            "envelope": {"format": "TEST_ONLY"},
            "transport": {"status": "TEST_ONLY_UNREVIEWED"},
            "zips": {"T": b"PKTEST-T", "A2": b"PKTEST-A2"},
        }
    source.update({
        "historical_merged_main_sha": M,
        "current_required_ci_accepted": False,
    })
    return {
        "phase": phase, "event": observed, "required": source,
        "envelope": None, "transport": None, "zips": {},
    }


class PhaseAwareStagedA2ConsumerTests(unittest.TestCase):
    def _execute(self, phase, *, altered=None, remove_zip=False):
        result = fabricated_result(phase)
        with tempfile.TemporaryDirectory(prefix="pr113-phase-a2-") as tmp:
            output, _ = runtime.store(result, Path(tmp) / "receipts", 111, 333)
            receipt = output / "historical_required.json"
            if remove_zip:
                for name in ("historical_T.zip", "historical_A2.zip"):
                    if (output / name).exists():
                        (output / name).unlink()
            if altered is not None:
                altered(receipt)
            env = {consumer.RECEIPT_ENV: str(receipt)}
            # Legacy input names deliberately absent: descendants must never
            # require them, while initials are checked via the real callee.
            with mock.patch.dict(os.environ, env, clear=False), \
                 mock.patch.object(runtime, "actual_source", return_value=event(phase)), \
                 mock.patch.object(runtime, "produce", return_value=result), \
                 redirect_stdout(io.StringIO()):
                for key in (
                    "PERMANSSON_DUAL_HISTORICAL_EVIDENCE",
                    "PERMANSSON_DUAL_ORIGINAL_T_ZIP",
                    "PERMANSSON_DUAL_ORIGINAL_A2_ZIP",
                ):
                    os.environ.pop(key, None)
                case = consumer.LocalizedCompilerIntegration(
                    "test_actual_final_source_and_semantic_mutations")
                case.test_actual_final_source_and_semantic_mutations()

    def test_all_four_lifecycle_phases_use_real_reauthentication(self):
        for phase in PHASES:
            with self.subTest(phase=phase):
                self._execute(phase)

    def test_initial_original_zip_missing_cannot_be_borrowed(self):
        with self.assertRaises(ValueError):
            self._execute("initial_113_pr", remove_zip=True)

    def test_descendant_does_not_require_initial_only_zip_variables(self):
        self._execute("main_descendant_pr")
        self._execute("main_descendant_push")

    def test_duplicate_json_keys_fail_at_intake(self):
        def duplicate(path):
            original = path.read_text(encoding="utf-8")
            path.write_text('{"phase":"FORGED",' + original.lstrip()[1:],
                            encoding="utf-8")
        with self.assertRaises(ValueError):
            self._execute("main_descendant_pr", altered=duplicate)

    def test_forged_source_or_phase_does_not_reauthenticate(self):
        def forged(path):
            payload = json.loads(path.read_text(encoding="utf-8"))
            payload["source_commit_sha"] = "f" * 40
            path.write_text(json.dumps(payload), encoding="utf-8")
        with self.assertRaises(runtime.RuntimeError113):
            self._execute("main_descendant_pr", altered=forged)

    def test_missing_phase_neutral_receipt_blocks(self):
        with mock.patch.dict(os.environ, {}, clear=True):
            case = consumer.LocalizedCompilerIntegration(
                "test_actual_final_source_and_semantic_mutations")
            with self.assertRaises(AssertionError):
                case.test_actual_final_source_and_semantic_mutations()

    def test_runtime_exports_one_phase_neutral_receipt_to_next_ci_step(self):
        """Synthetic event tests real main() output and GITHUB_ENV handoff."""
        for phase in PHASES:
            with self.subTest(phase=phase):
                result = fabricated_result(phase)
                with tempfile.TemporaryDirectory(prefix="pr113-export-") as temp:
                    envfile = Path(temp) / "github-env"
                    args = [
                        "--producer-run-id", "111",
                        "--security-review-id", "333",
                        "--out", str(Path(temp) / "material"),
                    ]
                    with mock.patch.dict(
                        os.environ, {"GITHUB_ENV": str(envfile)}, clear=False
                    ), mock.patch.object(
                        runtime, "produce", return_value=result
                    ), redirect_stdout(io.StringIO()):
                        self.assertEqual(runtime.main(args), 0)
                    lines = envfile.read_text(encoding="utf-8").splitlines()
                    paths = dict(line.split("=", 1) for line in lines)
                    self.assertEqual(
                        set(paths) >= {consumer.RECEIPT_ENV}, True)
                    receipt = Path(paths[consumer.RECEIPT_ENV])
                    self.assertTrue(receipt.is_file())
                    self.assertEqual(
                        json.loads(receipt.read_text())["phase"], phase)
                    original_vars = {
                        "PERMANSSON_DUAL_HISTORICAL_EVIDENCE",
                        "PERMANSSON_DUAL_ORIGINAL_T_ZIP",
                        "PERMANSSON_DUAL_ORIGINAL_A2_ZIP",
                    }
                    if phase.startswith("initial_113"):
                        self.assertTrue(original_vars <= set(paths))
                        for key in original_vars:
                            self.assertTrue(Path(paths[key]).is_file())
                    else:
                        self.assertTrue(original_vars.isdisjoint(paths))
