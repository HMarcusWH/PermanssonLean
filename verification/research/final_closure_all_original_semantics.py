"""Retain *candidate* source-bound Lean semantic negatives for all registered specs.

This is NOT independent acceptance or an authenticated CI review receipt.
It runs the already-frozen per-case source+mutant compiler process, sharded
over the exact registered candidate IDs, and retains their byte hashes.
The actual producing GitHub run/job must be authenticated separately.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

import final_closure_original_semantic_batch as batch
from final_closure_mutation_evidence import MutationEvidenceError, git_head

EXPECTED = frozenset((
    "F-03", "D-02", "D-03", "D-04", "D-05", "D-06",
    "Q-03", "Q-04", "E-05", "A-03", "C-01", "D-07",
    "E-01", "S-01", "M-01", "A-02", "D-01",
    "C11-01", "C11-02", "XPLUS-01",
    "S-02", "Q-01", "A-01", "A-04", "A-05",
))


def validate_candidate_case(head: str, cid: str, record: dict) -> dict:
    """A successful job must retain true/false execution, not just status.

    This checks the local producing payload before attaching any claimed CI
    identity. The external v3 authenticated producer still validates actual
    GitHub run/job/artifact and source/mutant ZIP bytes separately.
    """
    entry = batch.SPECS.get(cid)
    if not isinstance(entry, dict) or not isinstance(record, dict):
        raise MutationEvidenceError("original semantic case/record absent")
    expected = {
        "format": "Permansson.OriginalSemanticMutantCandidate.v1",
        "status": "DETACHED_UNREVIEWED_UNATTRIBUTED",
        "source_head": head,
        "case_id": cid,
        "test_path": entry["test_path"],
        "test_name": entry["method"],
        "source_path": entry["source"],
        "ci_check_run_id": None,
        "independent_review": False,
        "full_mathematical_acceptance": False,
    }
    if any(record.get(k) != v or type(record.get(k)) is not type(v)
           for k, v in expected.items()):
        raise MutationEvidenceError(
            "original semantic evidence returned foreign source/role/approval")
    hashes = ("mutant_sha256", "detached_bundle_sha256")
    if not all(isinstance(record.get(k), str) and
               re.fullmatch(r"[0-9a-f]{64}", record[k]) for k in hashes):
        raise MutationEvidenceError("original semantic source/ZIP digests absent")
    original = record.get("mutation_record")
    if (not isinstance(original, dict)
            or original.get("head_sha") != head
            or original.get("case_ids") != [cid]
            or original.get("claim_ids") != []
            or original.get("test_path") != entry["test_path"]
            or original.get("test_name") != entry["method"]
            or original.get("original_lean_source_path") != entry["source"]
            or original.get("mutant_source_sha256") != record["mutant_sha256"]
            or original.get("outcome") != "REJECTED_SEMANTIC"
            or type(original.get("compiler_exit_code")) is not int
            or original["compiler_exit_code"] == 0
            or original.get("check_run_id") is not None
            or original.get("review_status") != "NOT_RECEIVED"):
        raise MutationEvidenceError(
            "original semantic case lacks actual bound false Lean execution")
    positive = original.get("positive_control")
    if (not isinstance(positive, dict)
            or positive.get("compiled") is not True
            or positive.get("exit_code") != 0
            or not isinstance(positive.get("lean_toolchain"), str)
            or not re.fullmatch(r"[0-9a-f]{64}",
                                str(original.get("original_lean_source_sha256", "")))
            or not re.fullmatch(r"[0-9a-f]{64}",
                                str(original.get("source_sha256", "")))):
        raise MutationEvidenceError(
            "original positive Lean and exact source bytes were not retained")
    return original


def select_cases(shard_index: int, shard_count: int) -> tuple[str, ...]:
    if not 1 <= shard_count <= 25 or not 0 <= shard_index < shard_count:
        raise MutationEvidenceError("invalid original-semantic shard specification")
    if frozenset(batch.SPECS) != EXPECTED or len(batch.SPECS) != 25:
        raise MutationEvidenceError("registered source/mutant inventory changed")
    ordered = sorted(EXPECTED)
    return tuple(case for j, case in enumerate(ordered)
                 if j % shard_count == shard_index)


def run_exact_shard(head: str, shard_index: int, shard_count: int,
                    output: Path) -> dict:
    if not re.fullmatch(r"[0-9a-f]{40}", head) or git_head() != head:
        raise MutationEvidenceError("source head is not the checked-out Git object")
    output = output.resolve()
    root = batch.ROOT.resolve()
    if (output.exists() or output.is_relative_to(root) or
            root.is_relative_to(output)):
        raise MutationEvidenceError("untrusted/overlapping evidence output root")
    ids = select_cases(shard_index, shard_count)
    if not ids:
        raise MutationEvidenceError("semantic evidence shard has no assigned case")
    source_tree = subprocess.check_output(
        ["git", "rev-parse", "HEAD^{tree}"], cwd=root, text=True).strip()
    if not re.fullmatch(r"[0-9a-f]{40}", source_tree):
        raise MutationEvidenceError("invalid checked-out Git tree")
    output.mkdir(parents=True, exist_ok=False)
    completed = []
    for cid in ids:
        record = batch.run_one(head, cid, output / cid)
        validate_candidate_case(head, cid, record)
        (output / cid / "unreviewed_candidate.json").write_text(
            json.dumps(record, indent=2, sort_keys=True) + "\n",
            encoding="utf-8")
        completed.append({
            "case_id": cid,
            "source_sha256": record["mutation_record"]["original_lean_source_sha256"],
            "mutant_sha256": record["mutant_sha256"],
            "bundle_sha256": record["detached_bundle_sha256"],
            "status": record["status"],
        })
    # Rebind immutable source identity after the last real original-source
    # mutation execution. An externally observed source transition is a
    # failure, not a candidate with a borrowed old-H hash.
    if git_head() != head:
        raise MutationEvidenceError("Git HEAD changed during semantic execution")
    after_tree = subprocess.check_output(
        ["git", "rev-parse", "HEAD^{tree}"], cwd=root, text=True).strip()
    if after_tree != source_tree:
        raise MutationEvidenceError("Git source tree changed during semantic execution")
    ci_keys = ("GITHUB_REPOSITORY", "GITHUB_WORKFLOW", "GITHUB_JOB",
               "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT", "GITHUB_SHA")
    ci = {key: os.environ.get(key) for key in ci_keys}
    # The environment is a self-report until authenticated against the actual
    # GitHub job and uploaded artifact by the independent collector.
    manifest = {
        "format": "Permansson.AllOriginalSemanticCandidateShard.v1",
        "status": "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED_RECEIPT",
        "head": head,
        "tree": source_tree,
        "shard_index": shard_index,
        "shard_count": shard_count,
        "registered_candidate_count": len(EXPECTED),
        "case_ids": list(ids),
        "completed": completed,
        "github_environment_unverified": ci,
        "independent_review": False,
        "ci_check_run_id": None,
        "release_approved": False,
        "mathematical_acceptance": False,
    }
    payload = (json.dumps(manifest, sort_keys=True, indent=2) + "\n").encode()
    (output / "unreviewed_shard_manifest.json").write_bytes(payload)
    return {"status": manifest["status"], "head": head,
            "cases": list(ids), "manifest_sha256": hashlib.sha256(payload).hexdigest()}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--head", required=True)
    parser.add_argument("--shard-index", type=int, required=True)
    parser.add_argument("--shard-count", type=int, required=True)
    parser.add_argument("--out", type=Path, required=True)
    a = parser.parse_args(argv)
    try:
        result = run_exact_shard(a.head, a.shard_index, a.shard_count, a.out)
    except (MutationEvidenceError, OSError, ValueError,
            subprocess.CalledProcessError, KeyError) as e:
        print("DETACHED UNREVIEWED EVIDENCE BLOCKED:", e, file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
