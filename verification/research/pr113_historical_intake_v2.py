"""V2 historical ZIP *candidate* consumers: 25 historical / exact 30 current.

These pure parsers do not certify GitHub artifact provenance or human review.
Production must additionally check run/job/attempt/check/artifact identities
and source-bound reviewer authority. V1 receipts cannot upgrade to V2.
"""
from __future__ import annotations

from infrastructure_acceptance import (
    json_member, need, sha, verify_compiler_receipt,
    HISTORICAL_MUTATIONS, SUCCESSOR_MUTATIONS,
)
from pr113_semantic_receipt_v2 import validate_compiler_receipt_v2
from pr113_dual_tooling_candidate_v2 import validate_dual_reports_v2
from pr113_tooling_migration import T
import pr113_historical_a2_baseline_v1 as baseline
from localized_prefix_gate import DECLS

T2_FORMAT = "Permansson.PR113.DualToolingCandidate.v3"
DOSSIER_FORMAT = "Permansson.PR113.ToolingSecurityReviewDossier.v2"
A2_FORMAT = baseline.DUAL_FORMAT


def inspect_T_v2(files, head, *, profile_sha256):
    need(isinstance(head, str) and len(head) == 40 and
         isinstance(profile_sha256, str) and len(profile_sha256) == 64,
         "v2 T/T2 source or profile not supplied")
    old_raw = files.get("original_T_archive.json")
    current_raw = files.get("current_H_workflow.json")
    need(type(old_raw) is bytes and type(current_raw) is bytes,
         "versioned T2 requires both real underlying test reports")
    historical = json_member(files, "original_T_archive.json")
    current = json_member(files, "current_H_workflow.json")
    profile = {
        "format": "Permansson.PR113.ToolingMigrationCandidate.v2",
        "reviewed_workflow_source_mode": "active",
        "historical_original_workflow_count": 25,
        "current_reviewed_workflow_count": 30,
        "workflow_profile_sha256": profile_sha256,
        "independent_security_review": False,
    }
    checked = validate_dual_reports_v2(
        historical, current, T_source=T, H_source=head, profile=profile)
    receipt = json_member(files, "dual_tooling_unreviewed.json")
    dossier = json_member(files, "T2_security_review_candidate.json")
    need(checked["status"] == "DUAL_T_AND_30_H_EXECUTED_UNREVIEWED"
         and receipt.get("format") == T2_FORMAT
         and receipt.get("status") == checked["status"]
         and receipt.get("historical_T") == T
         and receipt.get("current_H") == head
         and receipt.get("genuine_current_source_commit") == head
         and receipt.get("original_T_archive_source_commit") == T
         and receipt.get("historical_original_workflow_count") == 25
         and receipt.get("current_reviewed_workflow_count") == 30
         and receipt.get("workflow_profile_sha256") == profile_sha256
         and receipt.get("historical_T_report_sha256") == sha(old_raw)
         and receipt.get("current_H_report_sha256") == sha(current_raw)
         and receipt.get("original_T_archive_unchanged") is True
         and receipt.get("independent_security_review") is False
         and receipt.get("versioned_successor_T2_approved") is False
         and dossier.get("format") == DOSSIER_FORMAT
         and dossier.get("status") ==
             "COMPLETE_DUAL_EXECUTION_CANDIDATE_SECURITY_REVIEW_PENDING"
         and dossier.get("T") == T
         and dossier.get("H") == head
         and dossier.get("historical_original_workflow_count") == 25
         and dossier.get("required_workflow_inventory_count") == 30
         and dossier.get("current_workflow_profile_sha256") == profile_sha256
         and dossier.get("T_original_offline_restore_report_sha256") ==
             sha(old_raw)
         and dossier.get("H_original_workflow_test_report_sha256") ==
             sha(current_raw)
         and dossier.get("legacy_T_did_not_accept_current_C") is True
         and dossier.get("owner_authorization_present") is False
         and dossier.get("independent_security_review_present") is False
         and dossier.get("historical_required_CI_replaced") is False
         and dossier.get("mathematical_release_approved") is False,
         "versioned original T/current 30 evidence incomplete, stale, or self-approved")
    return {
        "format": "Permansson.PR113.T2DualSourceCandidate.v2",
        "historical_T_report_sha256": sha(old_raw),
        "current_H_workflow_report_sha256": sha(current_raw),
        "T2_dossier_sha256": sha(files["T2_security_review_candidate.json"]),
        "historical_original_workflow_count": 25,
        "current_reviewed_workflow_count": 30,
        "current_workflow_profile_sha256": profile_sha256,
        "historical_T_unchanged": True,
        "independent_security_review": False,
        "mathematical_acceptance": False,
    }


def inspect_A2_v2(files, head):
    overall = json_member(files, "unreviewed_dual_A2_candidate.json")
    historical, hhash = validate_compiler_receipt_v2(
        files, "historical_original_A2",
        "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING", HISTORICAL_MUTATIONS)
    successor, shash = validate_compiler_receipt_v2(
        files, "pr113_successor_A2",
        "SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING", SUCCESSOR_MUTATIONS)
    baseline.verify_receipt_source(historical)
    need(set(historical.get("declarations", {})) == set(DECLS)
         and set(successor.get("declarations", {})) == set(DECLS),
         "both A2 legs must retain all forty original declarations")
    provenance = overall.get("historical_runtime_provenance")
    need(overall.get("format") == A2_FORMAT
         and overall.get("status") ==
             "BOTH_ACTUAL_A2_COMPILER_PATHS_EXECUTED_UNREVIEWED"
         and overall.get("historical_source_commit") == baseline.REPLAY_HEAD
         and overall.get("historical_introducer_sha") == baseline.INTRODUCER
         and overall.get("historical_tree_sha") == baseline.REPLAY_TREE
         and overall.get("current_source_commit") == head
         and overall.get("historical_original_workflow_count") == 25
         and overall.get("current_reviewed_workflow_count") == 30
         and overall.get("historical_test_executed") is True
         and overall.get("successor_test_executed") is True
         and overall.get("historical_signatures") == 40
         and overall.get("successor_signatures") == 40
         and overall.get("historical_semantic_mutants") == 4
         and overall.get("successor_semantic_mutants") == 4
         and overall.get("original_verifier_modified") is False
         and overall.get("independent_security_approval") is False
         and overall.get("independent_mathematical_approval") is False
         and overall.get("merged_main_sha") is None
         and overall.get("full_release_approved") is False
         and isinstance(provenance, dict)
         and provenance.get("imported_current_A2_gate") is False
         and provenance.get("historical_checkout_sha") == baseline.REPLAY_HEAD
         and provenance.get("historical_tree_sha") == baseline.REPLAY_TREE
         and provenance.get("introduced_executable_sha") == baseline.INTRODUCER
         and provenance.get("baseline_contract") == baseline.FORMAT
         and provenance.get("original_runtime_git_blobs") == baseline.EXECUTORS
         and provenance.get("output_receipt_sha256") == hhash
         and historical.get("source_unchanged") is True
         and successor.get("source_unchanged") is True
         and isinstance(successor.get("source"), dict)
         and successor["source"].get("git_head") == head
         and successor.get("format") ==
             "Permansson.PR113.A2SuccessorCompilerCandidate.v2",
         "A2 historical and active30 successor proof evidence not authenticated")
    return {
        "format": "Permansson.PR113.A2DualSourceCandidate.v3",
        "historical_introducer_sha": baseline.INTRODUCER,
        "historical_replay_sha": baseline.REPLAY_HEAD,
        "historical_replay_tree": baseline.REPLAY_TREE,
        "historical_A2_report_sha256": hhash,
        "successor_A2_report_sha256": shash,
        "dual_A2_sha256": sha(files["unreviewed_dual_A2_candidate.json"]),
        "historical_original_workflow_count": 25,
        "current_reviewed_workflow_count": 30,
        "independent_security_review": False,
        "mathematical_acceptance": False,
    }
