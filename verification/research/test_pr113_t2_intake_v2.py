"""V2 T2 receipt integration: real validators, synthetic inputs, no approvals."""
from __future__ import annotations

import copy
import hashlib
import json
import unittest

from infrastructure_acceptance import InfrastructureError
from pr113_dual_tooling_candidate_v2 import validate_dual_reports_v2
from pr113_historical_intake_v2 import inspect_T_v2

T = "71cc34fa0bc4b639c05d2ec5f39f0b88afd56388"
H = "a" * 40
DIGEST = "b" * 64


def encoded(obj):
    return (json.dumps(obj, sort_keys=True) + "\n").encode()


def reports():
    old = {
        "format": "Permansson.Hardening.Check.v1",
        "status": "PASS",
        "check": "archive-reproducibility",
        "context": {"checked_sha": T},
        "details": {
            "acceptance_scope": "accepted_artifact_replay_only",
            "isolation": {
                "network_isolation": "ENFORCED",
                "capabilities": "all_zero",
            },
        },
    }
    new = {
        "format": "Permansson.Hardening.Tests.v1",
        "schema_version": 1,
        "status": "PASS",
        "suite": "workflow",
        "execution_tracked_clean": True,
        "methods_run": 12,
        "failures": 0, "errors": 0, "skips": 0,
        "covered_requirements": ["CI-06", "CI-07"],
        "context": {
            "repository": "HMarcusWH/PermanssonLean",
            "checked_sha": H,
            "event": "local",
            "checked_tree": "c" * 40,
        },
    }
    profile = {
        "format": "Permansson.PR113.ToolingMigrationCandidate.v2",
        "reviewed_workflow_source_mode": "active",
        "historical_original_workflow_count": 25,
        "current_reviewed_workflow_count": 30,
        "workflow_profile_sha256": DIGEST,
        "independent_security_review": False,
    }
    return old, new, profile


def pieces():
    old, current, profile = reports()
    checked = validate_dual_reports_v2(
        old, current, T_source=T, H_source=H, profile=profile)
    original_raw = encoded(old)
    current_raw = encoded(current)
    receipt = {
        **checked,
        "candidate_execution_context": "LOCAL_UNREVIEWED",
        "historical_T_report_sha256": hashlib.sha256(original_raw).hexdigest(),
        "current_H_report_sha256": hashlib.sha256(current_raw).hexdigest(),
        "genuine_current_source_commit": H,
        "original_T_archive_source_commit": T,
        "original_T_archive_unchanged": True,
        "versioned_successor_T2_approved": False,
    }
    dossier = {
        "format": "Permansson.PR113.ToolingSecurityReviewDossier.v2",
        "status": "COMPLETE_DUAL_EXECUTION_CANDIDATE_SECURITY_REVIEW_PENDING",
        "T": T, "H": H,
        "historical_original_workflow_count": 25,
        "required_workflow_inventory_count": 30,
        "current_workflow_profile_sha256": DIGEST,
        "T_original_offline_restore_report_sha256":
            hashlib.sha256(original_raw).hexdigest(),
        "H_original_workflow_test_report_sha256":
            hashlib.sha256(current_raw).hexdigest(),
        "legacy_T_did_not_accept_current_C": True,
        "owner_authorization_present": False,
        "independent_security_review_present": False,
        "historical_required_CI_replaced": False,
        "mathematical_release_approved": False,
    }
    return {
        "original_T_archive.json": original_raw,
        "current_H_workflow.json": current_raw,
        "dual_tooling_unreviewed.json": encoded(receipt),
        "T2_security_review_candidate.json": encoded(dossier),
    }


class V2IntakeTests(unittest.TestCase):
    def test_exact_25_30_candidate_parses_without_claiming_approval(self):
        observed = inspect_T_v2(pieces(), H, profile_sha256=DIGEST)
        self.assertEqual(observed["current_reviewed_workflow_count"], 30)
        self.assertEqual(observed["historical_original_workflow_count"], 25)
        self.assertTrue(observed["historical_T_unchanged"])
        self.assertFalse(observed["independent_security_review"])
        self.assertFalse(observed["mathematical_acceptance"])

    def test_v1_receipt_must_not_promote_to_v2(self):
        elements = pieces()
        receipt = json.loads(elements["dual_tooling_unreviewed.json"])
        receipt["format"] = "Permansson.PR113.DualToolingCandidate.v2"
        elements["dual_tooling_unreviewed.json"] = encoded(receipt)
        with self.assertRaises(InfrastructureError):
            inspect_T_v2(elements, H, profile_sha256=DIGEST)

    def test_25_cannot_claim_current_30(self):
        elements = pieces()
        dossier = json.loads(elements["T2_security_review_candidate.json"])
        dossier["required_workflow_inventory_count"] = 25
        elements["T2_security_review_candidate.json"] = encoded(dossier)
        with self.assertRaises(InfrastructureError):
            inspect_T_v2(elements, H, profile_sha256=DIGEST)

    def test_foreign_profile_and_fabricated_review_rejected(self):
        with self.assertRaises(InfrastructureError):
            inspect_T_v2(pieces(), H, profile_sha256="0" * 64)
        elements = pieces()
        dossier = json.loads(elements["T2_security_review_candidate.json"])
        dossier["independent_security_review_present"] = True
        elements["T2_security_review_candidate.json"] = encoded(dossier)
        with self.assertRaises(InfrastructureError):
            inspect_T_v2(elements, H, profile_sha256=DIGEST)

    def test_missing_genuine_isolation_and_ci07_rejected(self):
        for corruption in ("isolation", "ci07"):
            old, current, profile = reports()
            if corruption == "isolation":
                old["details"]["isolation"]["network_isolation"] = "DISABLED"
            else:
                current["covered_requirements"] = ["CI-06"]
            with self.assertRaises(Exception):
                validate_dual_reports_v2(
                    old, current, T_source=T, H_source=H, profile=profile)
