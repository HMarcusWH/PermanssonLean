"""Source-bound bridge between 21 authenticated CI producers and strict v2 review.

The bridge binds each of 259 compiler receipts, 45 original semantic case
observations and 11 claims to the actual successful CI job that produced it.
It deliberately DOES NOT create v2 approval receipts: no historical verifier
is weakened, no global 'research' check is borrowed, and no independent
mathematical review is inferred from a green GitHub Actions job.
"""
from __future__ import annotations

import hashlib
import json
import re

SHA40 = re.compile(r"^[a-f0-9]{40}$")
SHA256 = re.compile(r"^[a-f0-9]{64}$")
AXIOMS = frozenset(("propext", "Classical.choice", "Quot.sound"))
WORKFLOWS = {
    "compiler": (".github/workflows/pr113-all-case-compiler.yml",
                 "pr113-compiler-shard-", 4),
    "append": (".github/workflows/pr113-all-original-semantic-candidates.yml",
               "pr113-all-original-semantic-candidates-", 9),
    "legacy": (".github/workflows/pr113-legacy-semantic-evidence.yml",
               "pr113-legacy-semantic-candidates-", 8),
}
FORMAT = "Permansson.PR113.ProducerBoundV2Preparation.v1"


class ProducerBindingError(ValueError):
    pass


def require(ok, reason):
    if not ok:
        raise ProducerBindingError(reason)


def canonical_sha(obj):
    return hashlib.sha256(json.dumps(
        obj, ensure_ascii=False, sort_keys=True,
        separators=(",", ":")).encode("utf-8")).hexdigest()


def verified_producer_index(head, producers):
    """Require the exact successful source-bound 4+9+8 producer partition."""
    require(isinstance(head, str) and SHA40.fullmatch(head),
            "invalid exact source H")
    require(isinstance(producers, list) and len(producers) == 21,
            "all 21 authenticated producing shards are required")
    by_shard = {}
    ids, checks, artifacts = set(), set(), set()
    for row in producers:
        require(isinstance(row, dict) and row.get("head_sha") == head and
                row.get("format") ==
                    "Permansson.PR113.AuthenticatedProducerArtifact.v1" and
                row.get("status") ==
                    "CI_ARTIFACT_DIGEST_VERIFIED_UNREVIEWED" and
                row.get("mathematical_acceptance") is False and
                row.get("independent_review") is False and
                row.get("scientific_release_approved") is False and
                row.get("merged_main_sha") is None,
                "stale/untrusted/approved producer attestation")
        for key in ("artifact_id", "actual_check_run_id",
                    "job_id", "run_id", "run_attempt"):
            require(type(row.get(key)) is int and row[key] > 0,
                    "missing actual producing identity: " + key)
        for key in ("artifact_sha256", "manifest_sha256"):
            require(isinstance(row.get(key), str) and
                    SHA256.fullmatch(row[key]),
                    "missing authoritative producing SHA256")
        name = row.get("artifact_name")
        path = row.get("workflow_path")
        matched = [
            (kind, int(name[len(prefix):]))
            for kind, (workflow, prefix, count) in WORKFLOWS.items()
            if type(name) is str and name.startswith(prefix)
            and name[len(prefix):].isdigit()
            and type(path) is str and path.endswith(workflow)
            and 0 <= int(name[len(prefix):]) < count
        ]
        require(len(matched) == 1, "unrecognized producing shard source")
        key = matched[0]
        require(key not in by_shard and row["artifact_id"] not in artifacts
                and row["job_id"] not in ids
                and row["actual_check_run_id"] not in checks,
                "duplicate/shadowed check or artifact identity")
        by_shard[key] = row
        artifacts.add(row["artifact_id"])
        ids.add(row["job_id"])
        checks.add(row["actual_check_run_id"])
    expected = {(kind, idx)
                for kind, (_workflow, _prefix, count) in WORKFLOWS.items()
                for idx in range(count)}
    require(set(by_shard) == expected, "missing or substituted producing shard")
    return by_shard


def producer_identity(row):
    return {
        "workflow_path": row["workflow_path"],
        "run_id": row["run_id"],
        "run_attempt": row["run_attempt"],
        "job_id": row["job_id"],
        "actual_producing_check_run_id": row["actual_check_run_id"],
        "artifact_id": row["artifact_id"],
        "artifact_name": row["artifact_name"],
        "artifact_sha256": row["artifact_sha256"],
        "manifest_sha256": row["manifest_sha256"],
    }


def bind(head, dossier, compiler, producers):
    """Build a reviewable, NOT-APPROVED receipt provenance crosswalk."""
    source = verified_producer_index(head, producers)
    require(isinstance(dossier, dict) and
            dossier.get("format") ==
                "Permansson.PR113.SourceReviewDossierCandidate.v1" and
            dossier.get("status") ==
                "UNREVIEWED_AUTHENTICATED_PRODUCERS_SCOPE_PENDING" and
            dossier.get("head_sha") == head and
            dossier.get("case_count") == 45 and
            dossier.get("claim_count") == 11 and
            dossier.get("compiler_target_count") == 259 and
            dossier.get("producer_count") == 21 and
            dossier.get("accepted_case_count") == 0 and
            dossier.get("accepted_claim_count") == 0 and
            dossier.get("independent_review") is False and
            dossier.get("release_approved") is False,
            "source review dossier is stale, incomplete or already promoted")
    tree = dossier.get("tree_sha")
    require(isinstance(tree, str) and SHA40.fullmatch(tree),
            "missing real frozen source tree")
    require(isinstance(compiler, dict) and
            compiler.get("head_sha") == head and
            compiler.get("status") == "COMPILER_ONLY_UNREVIEWED" and
            compiler.get("proof_count") == 259 and
            compiler.get("inventory_count") == 259 and
            compiler.get("case_count") == 45 and
            compiler.get("claim_count") == 11 and
            compiler.get("authentic_ci_job_bound") is False and
            compiler.get("independent_review") is False,
            "full source-owner compiler inventory unavailable or promoted")
    records = compiler.get("compiler_axiom_receipts")
    require(isinstance(records, list) and len(records) == 259,
            "missing exact 259 theorem records")
    all_cases = set()
    all_claims = set()
    accepted_proofs = {}
    bound_proofs = []
    for r in records:
        require(isinstance(r, dict) and
                type(r.get("inventory_index")) is int and
                0 <= r["inventory_index"] < 259 and
                r.get("id") == f'all:{r["inventory_index"]:04d}' and
                r.get("head_sha") == head and
                r.get("compiler_check") == "research" and
                r.get("compiler_result") == "PASS" and
                r.get("check_run_id") is None and
                r.get("axiom_log_member") ==
                    f'axiom_logs/all_{r["inventory_index"]:04d}.log' and
                isinstance(r.get("source_sha256"), str) and
                SHA256.fullmatch(r["source_sha256"]) and
                isinstance(r.get("axiom_log_sha256"), str) and
                SHA256.fullmatch(r["axiom_log_sha256"]) and
                isinstance(r.get("elaborated_type_sha256"), str) and
                SHA256.fullmatch(r["elaborated_type_sha256"]) and
                isinstance(r.get("universe_params_repr"), str) and
                bool(r["universe_params_repr"]) and
                isinstance(r.get("transitive_axioms"), list) and
                len(r["transitive_axioms"]) ==
                    len(set(r["transitive_axioms"])) and
                set(r["transitive_axioms"]) <= AXIOMS and
                isinstance(r.get("case_ids"), list) and
                isinstance(r.get("claim_ids"), list) and
                (r["case_ids"] or r["claim_ids"]),
                "missing, borrowed or untrusted exact-H Lean source proof")
        idx = r["inventory_index"]
        require(idx not in accepted_proofs, "duplicate source theorem index")
        accepted_proofs[idx] = r
        all_cases.update(r["case_ids"])
        all_claims.update(r["claim_ids"])
        producer = source[("compiler", idx % 4)]
        bound_proofs.append({
            "proof_id": r["id"], "inventory_index": idx,
            "source_path": r["path"],
            "qualified_declaration": r["declaration"],
            "source_sha256": r["source_sha256"],
            "elaborated_type_sha256": r["elaborated_type_sha256"],
            "transitive_axioms": list(r["transitive_axioms"]),
            "axiom_log_sha256": r["axiom_log_sha256"],
            "case_ids": list(r["case_ids"]),
            "claim_ids": list(r["claim_ids"]),
            "authenticated_producer": producer_identity(producer),
            "original_candidate_check_run_id": None,
            "strict_v2_proof_receipt": "PENDING_REAL_PRODUCER_TYPED_CONTRACT",
            "statement_header_sha256": None,
            "reviewed_mathematical_scope": False,
        })
    require(set(accepted_proofs) == set(range(259)),
            "incomplete/displaced all-case theorem indices")
    docket_cases = dossier.get("case_dockets")
    docket_claims = dossier.get("claim_dockets")
    require(isinstance(docket_cases, list) and len(docket_cases) == 45 and
            isinstance(docket_claims, list) and len(docket_claims) == 11,
            "case/claim review dockets incomplete")
    ids = set()
    bound_cases = []
    for row in docket_cases:
        cid = row.get("case_id") if isinstance(row, dict) else None
        require(isinstance(cid, str) and cid not in ids and
                row.get("accepted_case_decision") is None and
                row.get("semantic_scope_review_required") is True,
                "missing or preapproved original case")
        ids.add(cid)
        candidate = row.get("producing_negative_candidate")
        kind = candidate.get("route") if isinstance(candidate, dict) else None
        require(kind in ("append", "legacy") and
                isinstance(candidate.get("selected_semantic_methods"), list)
                and bool(candidate["selected_semantic_methods"]),
                "original case has no attributable semantic method")
        artifact_id = candidate.get("producing_artifact_id")
        producer = next((x for (k, _), x in source.items()
                         if k == kind and x["artifact_id"] == artifact_id), None)
        require(producer is not None and
                candidate.get(
                    "actual_producing_check_run_id_provenance_only") ==
                    producer["actual_check_run_id"] and
                candidate.get("accepted_semantic_negative") is False,
                "semantic case borrowed unrelated producing check/ZIP")
        proof_ids = [p["id"] for p in row.get("source_theorem_receipts", [])]
        require(bool(proof_ids) and
                all(any(cid in rec["case_ids"] and rec["id"] == proof_id
                        for rec in records) for proof_id in proof_ids),
                "case lacks source-owned theorem evidence: " + cid)
        bound_cases.append({
            "case_id": cid, "original_required_expected_result":
                row.get("original_required_expected_result"),
            "compiler_proof_ids": proof_ids,
            "negative_selected_methods":
                list(candidate["selected_semantic_methods"]),
            "negative_kind": kind,
            "authenticated_negative_producer": producer_identity(producer),
            "legacy_typed_source_replay_required": kind == "legacy",
            "strict_v2_positive_test_receipts": [],
            "strict_v2_negative_test_receipts": [],
            "independent_case_scope_review": None,
            "accepted_case_decision": None,
        })
    require(all_cases == ids and len(ids) == 45 and
            sum(c["negative_kind"] == "append" for c in bound_cases) == 25 and
            sum(c["negative_kind"] == "legacy" for c in bound_cases) == 20,
            "case scope or original 25/20 partition changed")
    known_claims = set()
    bound_claims = []
    for row in docket_claims:
        cid = row.get("claim_id") if isinstance(row, dict) else None
        require(isinstance(cid, str) and cid not in known_claims and
                row.get("accepted_claim_decision") is None and
                row.get("positive_negative_claim_receipts") == "NOT_ASSEMBLED" and
                row.get("independent_review") == "NOT_RECEIVED",
                "claim scope not pending or duplicate")
        known_claims.add(cid)
        proof_ids = row.get("compiler_receipt_ids")
        require(isinstance(proof_ids, list) and proof_ids and
                all(any(cid in rec["claim_ids"] and rec["id"] == proof_id
                        for rec in records) for proof_id in proof_ids),
                "claim missing one or more supporting compiler proofs")
        bound_claims.append({
            "claim_id": cid, "compiler_proof_ids": proof_ids,
            "selected_claim_tests": row.get("test_source_candidates", []),
            "strict_v2_positive_test_receipts": [],
            "strict_v2_negative_test_receipts": [],
            "independent_claim_review": None,
            "accepted_claim_decision": None,
        })
    require(all_claims == known_claims and len(known_claims) == 11,
            "original eleven claim owners incomplete")
    return {
        "format": FORMAT,
        "status": "AUTHENTIC_PRODUCER_CROSSWALK_UNREVIEWED_NOT_V2_ACCEPTANCE",
        "head_sha": head, "source_tree_sha": tree,
        "source_review_dossier_sha256": canonical_sha(dossier),
        "producer_artifact_count": 21,
        "proof_record_count": len(bound_proofs),
        "case_record_count": len(bound_cases),
        "claim_record_count": len(bound_claims),
        "proof_producers": bound_proofs,
        "case_producers": bound_cases,
        "claim_producers": bound_claims,
        "accepted_cases": 0, "accepted_claims": 0,
        "pending_explicit_review_scopes": 56,
        "global_required_ci_green": False,
        "strict_v2_ready": False,
        "actual_merged_main_sha": None,
        "mathematical_release_approved": False,
        "independent_review": False,
        "missing_v2_contract": [
            "real_producer_specific_check_authentication_in_strict_v2",
            "source_statement_header_hashes_for_259_declarations",
            "selected_positive_source_tests_for_45_original_cases",
            "valid_source_append_replays_for_20_legacy_cases",
            "individual_positive_and_negative_tests_for_11_new_claims",
            "real_independent_exact_H_45_case_and_11_claim_review",
            "all_required_source_checks_green",
            "historical_tooling_T_C_authorized_resolution",
            "actual_merge_M_postmerge_source_and_scholarly_authorization",
        ],
    }
