#!/usr/bin/env python3
"""Fail-closed post-PR102 source, acceptance and release evidence gates.

--mode audit checks 45 inherited cases, 42 contracts, immutable historical
records and current 124 provider source digests. It MAY pass with pending cases.
No GitHub-credential/network calls are required.
--mode full45-strict additionally needs all 45 verified and authenticated proof,
semantic-test, source-head/merge, CI and independent-review evidence.
--mode scoped-release-strict additionally binds an approved manuscript inventory
to the manifest and original full theorem crosswalk.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / "research/paper_closures/post_merge_102"
OLD = ROOT / "research/paper_closures/post_merge_79"
ALLOWED = {"VERIFIED_SELECTED_SCOPE", "VERIFIED_NEGATIVE", "PARTIAL_SCOPE", "PENDING", "BLOCKED"}
VERIFIED = {"VERIFIED_SELECTED_SCOPE", "VERIFIED_NEGATIVE"}
HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")
NOCHECK = ("UNVERIFIED", "PENDING", "NOT_RECEIVED", "RETIRED")
BASE = "3931e4dccafb47b3cdf70177c0cf337102c90731"


class EvidenceError(ValueError):
    pass


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise EvidenceError(reason)


def load_json(path: Path) -> dict:
    raw = path.read_bytes()
    require(raw.endswith(b"\n") and b"\r" not in raw, "noncanonical JSON: " + str(path))
    data = json.loads(raw)
    require(isinstance(data, dict), "expected JSON object: " + str(path))
    return data


def safe_path(base: Path, name: str) -> Path:
    p = Path(name)
    require(not p.is_absolute() and "\\" not in name and ".." not in p.parts,
            "unsafe source path " + name)
    full = (base / p).resolve()
    require(full.is_relative_to(base.resolve()), "source escaped repository")
    return full


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob(path: Path) -> str:
    return subprocess.check_output(["git", "hash-object", str(path)], cwd=ROOT,
                                   text=True, timeout=30).strip()


def validate_audit(*, decisions=None, index=None, crosswalk=None, reviews=None):
    ds = decisions or load_json(AUDIT / "acceptance_decisions.json")
    idx = index or load_json(AUDIT / "source_ci_index.json")
    cw = crosswalk or load_json(AUDIT / "theorem_crosswalk.json")
    rv = reviews or load_json(AUDIT / "review_receipts.json")
    old_decisions = load_json(OLD / "acceptance_decisions.json")
    old_index = load_json(OLD / "source_ci_index.json")
    old_norm = load_json(OLD / "receipt_normalization.json")
    for filename, historical in (("acceptance_decisions.json", old_decisions),
                                 ("source_ci_index.json", old_index),
                                 ("receipt_normalization.json", old_norm)):
        loc = OLD / filename
        require(git_blob(loc) == idx["original_historical_artifact_blobs"][filename],
                "historical PR79 file mutated: " + filename)
    require(ds.get("evaluated_main_sha") == idx.get("evaluated_main_sha") == BASE,
            "wrong original post102 baseline")
    require(idx["evaluated_main_tree"] == "0ffd313dcd5efd1cf90a85ee458024b1b28cd3f8",
            "wrong baseline tree")
    require(ds["historical_case_count"] == 45 and len(ds["cases"]) == 45,
            "historical 45-case count mismatch")
    ids = [case["case_id"] for case in ds["cases"]]
    expected = [case["id"] for case in old_decisions["cases"]]
    require(len(set(ids)) == 45 and sorted(ids) == sorted(expected),
            "missing/extra/duplicate required case")
    require(ds["pending_strengthened_historical_ids"] == old_decisions["pending_ids"],
            "historical unresolved-strengthened list altered")
    require(ds["full45_accepted"] is False and ds["scoped_release_accepted"] is False,
            "unreviewed baseline cannot be marked accepted")
    old_cases = {row["id"]: row for row in old_decisions["cases"]}
    old_contracts = {row["id"]: row for row in old_index["contracts"]}
    for case in ds["cases"]:
        old = old_cases[case["case_id"]]
        require(case["decision"] in ALLOWED, "unknown acceptance status")
        require(case["historical_contract_ids"] == old["atlas_ids"],
                "historical atlas mapping changed: " + case["case_id"])
        require(case["required_expected_result"] == old["required_expected_result"],
                "original acceptance requirement rewritten: " + case["case_id"])
        require(case["decision"] not in VERIFIED or bool(case["positive_tests"] and
                  case["negative_tests"] and case["ci_receipts"] and
                  case["review_receipts"]), "unearned verification promotion")
        all_decl = [d for t in old_index["contracts"] if case["case_id"] in
                    t["acceptance_ids"] for d in t["declarations"]]
        pinned = {(d["path"], d["declaration"]) for d in all_decl}
        actual = {(d["path"], d["name"]) for d in case["proof_declarations"]}
        require(pinned == actual,
                "historical declaration binding missing/changed: " + case["case_id"])
        for d in case["proof_declarations"]:
            original = next(v for v in all_decl if v["path"] == d["path"]
                            and v["declaration"] == d["name"])
            require(d["historical_source_sha256"] == original["source_sha256"],
                    "historical source pin changed: " + case["case_id"])
        require(len(case["remaining_obligations"]) > 0 or case["decision"] in VERIFIED,
                "unresolved requirement erased: " + case["case_id"])
    require(cw["historical_contract_count"] == 42 and len(cw["contracts"]) == 42,
            "wrong historical contract count")
    require(sorted(c["atlas_id"] for c in cw["contracts"]) ==
            sorted(old_contracts), "atlas IDs changed")
    for c in cw["contracts"]:
        o = old_contracts[c["atlas_id"]]
        require(c["historical_selected_scope"] == o["selected_scope"] and
                c["acceptance_case_ids"] == o["acceptance_ids"] and
                c["historical_declared_hypotheses"] == o["required_hypotheses"],
                "theorem historical scope rewritten")
    require(len(idx["current_verified_source_sha256"]) ==
            len({x["path"] for t in old_index["contracts"] for x in t["declarations"]}),
            "missing historical source")
    expected_digests = {}
    for t in old_index["contracts"]:
        for d in t["declarations"]:
            path, digest = d["path"], d["source_sha256"]
            require(path not in expected_digests or expected_digests[path] == digest,
                    "conflicting historical hashes")
            expected_digests[path] = digest
    indexed = {x["path"]: x["sha256"] for x in idx["current_verified_source_sha256"]}
    require(len(indexed) == len(idx["current_verified_source_sha256"]) and
            indexed == expected_digests, "missing/altered source index digest")
    for path, digest in indexed.items():
        require(bool(HEX64.fullmatch(digest)), "invalid source sha256")
        loc = safe_path(ROOT, path)
        require(loc.is_file() and sha256(loc) == digest, "source changed: " + path)
    require(idx["historical_constitutioncore_receipt"] ==
            "RETIRED_UNRECONCILED_OWNER_RECEIPT_BINDING",
            "historical unresolved receipt laundered")
    require(idx["original_17_679_census"] == "UNVERIFIED_DO_NOT_CITE",
            "historically unlocated receipt promoted")
    require(rv["receipts"] == idx["review_receipts"] == [],
            "unverified external review receipt fabricated")
    return {"cases":len(ids), "sources":len(indexed), "contracts":len(old_contracts),
            "pending":sum(x["decision"] not in VERIFIED for x in ds["cases"])}


def require_authenticated_strict(ds: dict, idx: dict, rv: dict) -> None:
    require(all(c["decision"] in VERIFIED for c in ds["cases"]),
            "at least one mandatory 45-case requirement is unresolved")
    for sha in ("branch_head_sha", "pr_synthetic_merge_sha", "post_merge_main_sha"):
        require(isinstance(idx[sha], str) and HEX40.fullmatch(idx[sha]),
                "missing B/H/S/M authenticated source identity: " + sha)
    require(idx["ci_receipts"] and idx["review_receipts"] and rv["receipts"],
            "missing real source-bound CI/review evidence")
    for case in ds["cases"]:
        require(case["positive_tests"] and case["negative_tests"] and
                case["ci_receipts"] and case["review_receipts"],
                "case lacks required test/proof provenance: " + case["case_id"])
        for proof in case["proof_declarations"]:
            require(proof["source_sha256"] and proof["statement_sha256"] and
                    proof["reviewed_head_sha"] == idx["branch_head_sha"],
                    "unverified theorem statement/source: " + case["case_id"])
    require(rv["independent_human_or_academic_peer_review"] != "NOT_CLAIMED",
            "independent review not authenticated")


def verify(mode: str, manifest_path: str | None=None) -> dict:
    summary = validate_audit()
    if mode == "audit":
        return summary
    ds = load_json(AUDIT / "acceptance_decisions.json")
    idx = load_json(AUDIT / "source_ci_index.json")
    rv = load_json(AUDIT / "review_receipts.json")
    if mode == "full45-strict":
        require_authenticated_strict(ds, idx, rv)
        return summary
    require(mode == "scoped-release-strict", "unknown verification mode")
    require(manifest_path, "scoped release requires --manifest")
    manifest = load_json(safe_path(ROOT, manifest_path))
    require(manifest.get("status") == "APPROVED_SOURCE_BOUND",
            "draft/unapproved mathematical release")
    require(manifest.get("source_commit_sha") == idx["post_merge_main_sha"] and
            isinstance(idx["post_merge_main_sha"], str) and
            HEX40.fullmatch(idx["post_merge_main_sha"]),
            "release source commit not bound to actual integrated proof tree")
    require(manifest.get("claims") and manifest.get("approved_manuscript_claims"),
            "no frozen approved manuscript/claim inventory")
    require(set(manifest["claims"]) == set(manifest["approved_manuscript_claims"]),
            "paper claims omitted from manifest")
    require(manifest.get("accepted_claim_receipts") and
            manifest.get("source_ci_receipts") and manifest.get("review_receipts"),
            "missing signed scope/review/CI receipts")
    require(manifest.get("scientific_limitations") and
            manifest.get("empirical_identification_status"),
            "unqualified scientific claim boundary")
    return summary


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("audit","full45-strict","scoped-release-strict"),
                        default="audit")
    parser.add_argument("--manifest")
    args = parser.parse_args(argv)
    try:
        summary = verify(args.mode,args.manifest)
    except (EvidenceError, OSError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        print("NOT ACCEPTED: " + str(exc), file=sys.stderr)
        return 2
    print("PASS: " + args.mode + " " + json.dumps(summary,sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
