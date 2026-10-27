"""Mandatory original-v3 + v3.1 executed-source gate (read-only).

No JSON label here grants review or mathematical certification. Before a
strict premerge/postmerge acceptance result, this routine independently
reattributes every new owner to authentic exact-H GitHub runs, jobs, checks,
workflow Git blobs and original downloaded artifact ZIPs, then re-examines
the raw positive and intended false-source compiler/test bytes. The original
21 producer ZIPs remain mandatory and independently authenticated.
"""
from __future__ import annotations

from collections import Counter
import json
from pathlib import Path

from final_closure_authenticate import git
from final_closure_case_receipts import (
    ROOT, authenticate_v3_sources, EvidenceError,
)
from final_closure_legacy_semantic_evidence import original_case_map
from final_closure_extra_producers_v31 import (
    candidate_registry, expected_controls, authenticated_extra_controls,
    ControlProducerError,
)
from final_closure_mutation_evidence import committed_file_bytes
from pr113_boundary_io import strict_json_object, detached_destination
from pr113_v31_execution_integrity import (
    exact_source, validate_executed_controls, RealControlError,
)


class MandatoryV31Error(ValueError):
    pass


def need(condition, message):
    if not condition:
        raise MandatoryV31Error(message)


def external(path, *, directory=False):
    src = Path(path)
    need(".." not in src.parts,
         "parent-traversing owner evidence path")
    src = src.resolve(strict=True)
    need(not src.is_relative_to(ROOT.resolve()) and
         not ROOT.resolve().is_relative_to(src) and
         (src.is_dir() if directory else src.is_file()),
         "control source files must be detached from the Git checkout")
    return src


def read_object(path):
    raw = external(path).read_bytes()
    need(0 < len(raw) <= 4 * 1024 * 1024, "oversized or missing control JSON")
    obj = strict_json_object(raw)
    need(isinstance(obj, dict), "malformed control producer JSON")
    return obj


def authenticate_all_76(head, original_receipts, original_members, *,
                         additional_contract, additional_zips,
                         workflow_blob_candidates):
    """Return only real authenticated *execution* provenance, never approval.

    Call after verify_premerge() or verify_merged_v2() authenticates exact H,
    required source-head and/or M checks and independent review scopes.
    This routine works both from a genuine H checkout and later genuine M
    whose verified source tree equals the signed H tree.
    """
    need(isinstance(head, str) and len(head) == 40 and
         isinstance(original_receipts, dict) and
         original_receipts.get("head_sha") == head and
         original_receipts.get("format") ==
             "Permansson.FinalClosureDetachedReceipts.v3" and
         isinstance(original_members, dict),
         "full-source gate requires real original exact-H v3 members")
    need(git("cat-file", "-t", head) == "commit",
         "original reviewed H Git object unavailable")
    try:
        authentic_original = authenticate_v3_sources(
            original_receipts, head, original_members)
        need(authentic_original.get("status") ==
             "REAL_PRODUCING_BYTES_UNREVIEWED" and
             authentic_original.get("head_sha") == head and
             authentic_original.get("producer_count") == 21,
             "the 21 original real source-control artifact ZIPs are incomplete")
        by_case, legacy = original_case_map(head)
        claim_path = ROOT / ("research/paper_closures/post_merge_112/"
                             "claim_declaration_map.json")
        claims = strict_json_object(committed_file_bytes(
            head, claim_path, root=ROOT))
        claim_ids = [r.get("claim_id") for r in claims.get("claims", [])]
        expected = expected_controls(
            list(by_case), legacy, claim_ids)
        need(len(expected) == 76,
             "original 45 case/20 legacy/11 claim source ownership corrupted")
        proposal = read_object(additional_contract)
        jobs = candidate_registry(proposal, head, expected)
        root = external(additional_zips, directory=True)
        names = {str(j["artifact_id"]) + ".zip" for j in jobs}
        need({p.name for p in root.iterdir()} == names,
             "extra producer ZIP directory has a missing or foreign artifact")
        bytes_by_id, total = {}, 0
        for job in jobs:
            path = external(root / (str(job["artifact_id"]) + ".zip"))
            raw = path.read_bytes()
            need(0 < len(raw) <= 64 * 1024 * 1024,
                 "missing or oversized original source-control ZIP")
            total += len(raw)
            need(total <= 256 * 1024 * 1024,
                 "original source-control ZIPs exceed bounded input")
            bytes_by_id[job["artifact_id"]] = raw
        workflow_blobs = read_object(workflow_blob_candidates)
        attributed = authenticated_extra_controls(
            head, proposal, bytes_by_id,
            original_producers=authentic_original,
            original_bundle_sha256=original_receipts.get(
                "evidence_bundle_sha256"),
            expected=expected,
            reviewed_workflow_blobs=workflow_blobs)
        execution = validate_executed_controls(
            head, proposal, bytes_by_id, source=exact_source(head, ROOT),
            original_producers=authentic_original)
        need(attributed.get("head_sha") == head and
             attributed.get("status") ==
                "ALL_ADDITIONAL_CONTROLS_SOURCE_ATTRIBUTED_UNREVIEWED" and
             len(attributed.get("source_owned_controls", [])) == 76 and
             execution.get("status") ==
                "ACTUAL_CONTROL_BYTES_REVALIDATED_UNREVIEWED" and
             execution.get("source_owner_count") == 76 and
             execution.get("claim_positive_negative_directions") == 22 and
             execution.get("canonical_routes_bound") is True and
             execution.get("legacy_original_captures_bound") is True and
             attributed.get("schema_security_approved") is False and
             attributed.get("independent_mathematical_review") is False,
             "additional true/false source evidence is incomplete or self-approved")
        seen = {(row["kind"], row["owner_id"])
                for row in attributed["source_owned_controls"]}
        need(seen == expected, "authenticated producer owner partition differs")
    except (EvidenceError, ControlProducerError, RealControlError,
            KeyError, TypeError, OSError, ValueError) as exc:
        raise MandatoryV31Error(
            "genuine source-control 76-owner authentication failed: " +
            str(exc)) from exc
    return {
        "format": "Permansson.PR113.StrictAdditionalSourceGate.v3.1",
        "status": "SOURCE_EXECUTION_AUTHENTICATED_REVIEW_SEPARATE",
        "head_sha": head,
        "original_artifacts": 21,
        "additional_owners": 76,
        "original_case_positives": 45,
        "legacy_case_negatives": 20,
        "claim_pairs": 11,
        "claim_directions": 22,
        "execution_log_members_verified":
            execution["execution_log_members_checked"],
        "independent_security_approval": False,
        "independent_math_approval": False,
        "publication_authorized": False,
    }
