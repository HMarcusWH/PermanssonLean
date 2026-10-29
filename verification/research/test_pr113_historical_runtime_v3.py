"""The authenticated v3 historical adapter cannot borrow the original scope.

All fixture decisions below are synthetically constructed *only* to exercise
the routing and output parser. No acceptance or GitHub approval is asserted.
"""
from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import pr113_historical_runtime_v3 as adapter
import pr113_historical_inheritance_v3 as inheritance

H = "b" * 40
M = "c" * 40
C = "d" * 40


def event(phase):
    return {
        "phase": phase, "source_commit_sha": C,
        "github_run_id": 222, "github_run_attempt": 1,
        "base_sha": "17c315f7df7abf457eb94d393bd526d46da6f6f4",
        "head_sha": H, "synthetic_sha": C,
        "infrastructure_head_sha": H,
        "infrastructure_merge_sha": M if phase != "initial_113_pr" else None,
    }


class HistoricalLifecycleUnitTests(unittest.TestCase):
    def test_descendant_uses_original_M113_source_revalidation(self):
        current = event("main_descendant_pr")
        original = {
            "format": inheritance.FORMAT,
            "status": "PR113_HISTORICAL_SOURCE_REVERIFIED_FOR_AUTHENTIC_DESCENDANT",
            "historical_merged_main_sha": M,
            "current_required_ci_accepted": False,
        }
        with mock.patch.object(adapter, "inherited_verify",
                               return_value=original) as source:
            result = adapter.produce(111, 333, event=current)
        self.assertEqual(result["required"], original)
        self.assertEqual(result["zips"], {})
        self.assertIsNone(result["envelope"])
        source.assert_called_once_with(111, 333, lifecycle=current)

    def test_original_PR_requires_authentic_v2_security_source(self):
        current = event("initial_113_pr")
        original = {"envelope": {"format": "mock_original"},
                    "zips": {"T": b"PK_t", "A2": b"PK_a2"},
                    "transport": {"status": "REVIEW_PENDING"}}
        with mock.patch(
            "pr113_historical_artifact_delivery_v2.deliver",
            return_value=original), mock.patch(
            "pr113_required_dual_gate_v2.verify",
            return_value={"independent_security_review_authenticated": True}):
            result = adapter.produce(111, 333, event=current)
        self.assertEqual(result["phase"], "initial_113_pr")
        self.assertFalse(result["required"].get("publication_authorized", False))

    def test_reject_unrecognized_lifecycle(self):
        with self.assertRaises(adapter.RuntimeError113):
            adapter.produce(111, 333, event=event("stale_foreign_branch"))

    def test_unbound_receipt_and_borrowed_original_ids_reject(self):
        current = event("main_descendant_pr")
        with tempfile.TemporaryDirectory() as tmp:
            file = Path(tmp) / "historical.json"
            base = {
                "format": adapter.FORMAT,
                "phase": current["phase"],
                "source_commit_sha": C,
                "original_github_run_id": 222,
                "original_github_run_attempt": 1,
                "historical_producer_run_id": 111,
                "historical_security_review_id": 333,
                "accepted_current_mathematics": False,
                "owner_merge_authorized": False,
                "publication_authorized": False,
                "historical_required_result": {
                    "status": "PR113_HISTORICAL_SOURCE_REVERIFIED_FOR_AUTHENTIC_DESCENDANT",
                    "historical_merged_main_sha": M,
                    "current_required_ci_accepted": False,
                },
            }
            file.write_text(json.dumps(base))
            # Only a synthetic test replay: production rechecks original GitHub.
            valid_fresh = {
                "phase": current["phase"], "event": current,
                "required": base["historical_required_result"],
                "envelope": None, "transport": None, "zips": {},
            }
            def simulated(*args, **kwargs):
                self.assertEqual(args, (111, 333))
                self.assertEqual(kwargs, {"event": current})
                return valid_fresh
            adapter.check_stored(file, 111, 333, event=current,
                                 recompute=simulated)
            for change in (
                {"historical_security_review_id": 445},
                {"source_commit_sha": "f" * 40},
                {"accepted_current_mathematics": True},
                {"historical_required_result": {
                    "status": "FORGED_SUCCESS",
                    "historical_merged_main_sha": M,
                    "current_required_ci_accepted": False}},
            ):
                candidate = {**base, **change}
                file.write_text(json.dumps(candidate))
                with self.subTest(change=change), self.assertRaises(
                        adapter.RuntimeError113):
                    adapter.check_stored(file, 111, 333, event=current,
                                         recompute=simulated)

    def test_structurally_valid_but_borrowed_receipt_is_rejected(self):
        current = event("main_descendant_pr")
        with tempfile.TemporaryDirectory() as tmp:
            file = Path(tmp) / "historical.json"
            source = {
                "status": "PR113_HISTORICAL_SOURCE_REVERIFIED_FOR_AUTHENTIC_DESCENDANT",
                "historical_merged_main_sha": M, "current_required_ci_accepted": False,
            }
            payload = {
                "format": adapter.FORMAT, "phase": current["phase"],
                "source_commit_sha": C, "original_github_run_id": 222,
                "original_github_run_attempt": 1, "historical_producer_run_id": 111,
                "historical_security_review_id": 333,
                "accepted_current_mathematics": False, "owner_merge_authorized": False,
                "publication_authorized": False, "historical_required_result": source,
            }
            file.write_text(json.dumps(payload))
            forged_recompute = {
                "phase": current["phase"], "event": current,
                "required": {**source, "historical_original_producer_run_id": 444},
                "envelope": None, "transport": None, "zips": {},
            }
            with self.assertRaises(adapter.RuntimeError113):
                adapter.check_stored(file, 111, 333, event=current,
                                     recompute=lambda *a, **k: forged_recompute)
            file.unlink()
            file.symlink_to(Path(tmp) / "elsewhere.json")
            with self.assertRaises(ValueError):
                adapter.check_stored(file, 111, 333, event=current,
                                     recompute=lambda *a, **k: forged_recompute)

    def test_inherited_source_result_requires_12_authenticated_contexts(self):
        current = event("main_descendant_pr")
        info = {
            "source_head_sha": H, "merged_main_sha": M,
            "historical_original_producer_run_id": 111,
            "security_review_id": 333,
            "historical_status":
                "MERGED_HISTORICAL_T_AND_A2_REVERIFIED_UNDER_REVIEWED_SOURCE",
            "historical_original_workflow_count": 25,
            "current_reviewed_workflow_count": 30,
            "original_required_context_count": 12,
            "historical_security_review_authenticated": True,
            "historical_T_and_A2_genuine": True,
            "new_mathematical_acceptance": False,
            "publication_authorized": False,
        }
        valid = inheritance.verify_child_report(
            info, current, run_id=111, reviewer_id=333)
        self.assertFalse(valid["new_mathematical_acceptance"])
        for mutation in (
            {"original_required_context_count": 11},
            {"historical_security_review_authenticated": False},
            {"historical_T_and_A2_genuine": False},
            {"merged_main_sha": "f" * 40},
            {"publication_authorized": True},
        ):
            with self.subTest(mutation=mutation), self.assertRaises(
                    inheritance.InheritanceError):
                inheritance.verify_child_report(
                    {**info, **mutation}, current, run_id=111,
                    reviewer_id=333)
