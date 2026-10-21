#!/usr/bin/env python3
"""Fail-closed final mathematical-closure acceptance verifier.

An audit PASS means a complete and truthful candidate snapshot, not theorem
acceptance. Strict modes require a *separately authenticated* final-head,
synthetic-merge, merged-main and independent reviewer record. Offline audit needs no network; strict modes authenticate live GitHub CI/review and local Git objects.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from final_closure_authenticate import verify_source, verify_merged_v2, AuthenticationError
from final_closure_case_receipts import (
    FORMAT as DETACHED_FORMAT, EvidenceError,
    load_detached_bundle, effective_acceptance,
)
import post_merge_102_verify as historical_audit
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
NEW = ROOT / "research/paper_closures/post_merge_112"
OLD = ROOT / "research/paper_closures/post_merge_79"
PREV = ROOT / "research/paper_closures/post_merge_102"
VERIFIED = {"VERIFIED_SELECTED_SCOPE", "VERIFIED_NEGATIVE"}
STATUSES = VERIFIED | {"PENDING", "PARTIAL_SCOPE", "BLOCKED"}
SHA40 = re.compile(r"^[a-f0-9]{40}$")
SHA256 = re.compile(r"^[a-f0-9]{64}$")
BASE = "17c315f7df7abf457eb94d393bd526d46da6f6f4"


class GateError(ValueError):
    pass


def check(test: bool, message: str) -> None:
    if not test:
        raise GateError(message)


def read_json(path: Path) -> dict:
    obj = json.loads(path.read_bytes())
    check(isinstance(obj, dict), f"not a JSON object: {path}")
    return obj


def secure_path(path: str) -> Path:
    p = Path(path)
    check(not p.is_absolute() and ".." not in p.parts and "\\" not in path,
          f"unsafe path: {path}")
    candidate = (ROOT / p).resolve()
    check(candidate.is_relative_to(ROOT.resolve()), f"escaped repo: {path}")
    return candidate


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def current_git_head() -> str | None:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT,
            stderr=subprocess.DEVNULL, text=True, timeout=15).strip()
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired):
        return None


def audit() -> dict:
    # Keep the original 124-provider historical SHA and case-source checks
    # as an independent precondition; never replace a preserved audit.
    historical_audit.validate_audit()
    decisions = read_json(NEW / "acceptance_decisions.json")
    cross = read_json(NEW / "theorem_crosswalk.json")
    inv = read_json(NEW / "claim_inventory.json")
    index = read_json(NEW / "source_ci_index.template.json")
    reviews = read_json(NEW / "review_receipts.json")
    historical = read_json(OLD / "acceptance_decisions.json")
    prev = read_json(PREV / "acceptance_decisions.json")
    original = {row["id"]: row for row in historical["cases"]}
    prevmap = {row["case_id"]: row for row in prev["cases"]}
    cases = decisions.get("cases", [])
    check(len(cases) == len(original) == 45, "45-case count mismatch")
    ids = [r["case_id"] for r in cases]
    check(len(set(ids)) == 45 and set(ids) == set(original),
          "lost, extra or duplicate original acceptance case")
    check(all(v.get("source_baseline_sha") == BASE for v in
              (decisions, cross, index, inv)), "wrong source baseline")
    check(index["source_baseline_tree"] ==
          "1bd1c31a67d28c97b82d6234d6c013b31336a0fd",
          "incorrect original tree")
    check(cross.get("historical_contract_count") == 42 and
          len(cross.get("contracts", [])) == 42,
          "the 42 original atlas contracts are missing")
    check(len(cross.get("closure_additions", [])) == 11,
          "missing one of the planned closure obligations")
    check(len(inv.get("claims", [])) == 11, "claim inventory mismatch")
    check(reviews.get("independent_review") is False or
          bool(reviews.get("academic_reviews")),
          "fabricated independent review")
    check(index.get("historical_receipt_limits", {}).get(
          "original_17_679_census") == "UNVERIFIED_DO_NOT_CITE",
          "unverified historical census promoted")
    check(index.get("historical_receipt_limits", {}).get(
          "constitution_core") == "RETIRED_UNRECONCILED_OWNER_RECEIPT_BINDING",
          "unreconciled historical source binding promoted")
    for row in cases:
        cid = row["case_id"]
        check(row["decision"] in STATUSES, f"unknown decision for {cid}")
        check(row["required_expected_result"] ==
              original[cid]["required_expected_result"],
              f"weakened original expected result: {cid}")
        check(row["historical_contract_ids"] == original[cid]["atlas_ids"],
              f"changed original atlas binding: {cid}")
        check(row["historical_contract_ids"] ==
              prevmap[cid]["historical_contract_ids"],
              f"changed historical case definition: {cid}")
        check(row["proof_declarations"] == prevmap[cid]["proof_declarations"],
              f"historical theorem statement/source pin mutated: {cid}")
        # A tracked source candidate cannot contain future exact-H reviewer
        # approvals. Approved decisions are DETACHED and authenticated live.
        # Nonempty strings or locally forged receipt arrays never suffice.
        check(row["decision"] not in VERIFIED,
              f"source-embedded acceptance bypasses detached review: {cid}")
        check(bool(row.get("remaining_obligations")),
              f"unresolved case with no requirements: {cid}")
    for c in cross["closure_additions"]:
        path = secure_path(c["path"])
        check(c["id"] in {e["id"] for e in inv["claims"]},
              f"undeclared closure {c['id']}")
        if c["status"] not in {"PLANNED_NOT_VERIFIED", "NOT_LEAN_VERIFIED", "VERIFIED_SELECTED_SCOPE", "BLOCKED"}:
            raise GateError(f"unknown closure status: {c['id']}")
        if c["status"] == "VERIFIED_SELECTED_SCOPE":
            check(path.exists() and SHA256.fullmatch(c.get("source_sha256") or "") and
                  digest(path) == c["source_sha256"] and
                  bool(c["actual_declarations"] and c["axiom_receipts"]),
                  f"unsubstantiated theorem status: {c['id']}")
    return {"cases": 45, "contracts": 42, "closures": 11,
            "verified": sum(r["decision"] in VERIFIED for r in cases),
            "pending": sum(r["decision"] not in VERIFIED for r in cases),
            "audit": "PASS_WITH_DECLARED_PENDING"}



def verify_claim_source_receipts(receipts: dict, source_head: str) -> set[str]:
    """Bind claimed Lean theorems and false-semantic mutants to actual bytes.

    Live GitHub's successful Research Lean check is separately authenticated
    by verify_source(). Here we prevent a caller from substituting unrelated
    statements, stale files, or a parser failure as an accepted theorem test.
    """
    proofs = receipts.get("compiler_axiom_receipts", [])
    negatives = receipts.get("semantic_negative_receipts", [])
    check(isinstance(proofs, list) and bool(proofs) and
          isinstance(negatives, list) and bool(negatives),
          "missing theorem proofs or semantic negative evidence")
    verified = set()
    for row in proofs:
        check(isinstance(row, dict), "malformed theorem receipt")
        path = secure_path(row.get("path", ""))
        check(path.is_file() and path.suffix == ".lean",
              "theorem receipt does not refer to an existing Lean module")
        check(digest(path) == row.get("source_sha256") and
              row.get("head_sha") == source_head,
              "unbound Lean source or stale proof head: " + str(path))
        name = row.get("declaration")
        check(isinstance(name, str) and bool(name) and
              re.fullmatch(r"[A-Za-z0-9_'.]+", name),
              "invalid Lean declaration name")
        local = name.rsplit(".", 1)[-1]
        pattern = (r"(?m)^\s*(?:private\s+|protected\s+)?"
                   r"(?:(?:noncomputable|unsafe)\s+)?"
                   r"(?:theorem|lemma|def)\s+" + re.escape(local) + r"(?=\W)")
        content = path.read_text(encoding="utf-8")
        match = re.search(pattern, content)
        check(match is not None, "claimed theorem declaration absent: " + name)
        end = content.find(":=", match.end())
        check(end > match.end(), "missing theorem statement separator: " + name)
        statement = content[match.start():end].strip()
        check(hashlib.sha256(statement.encode("utf-8")).hexdigest() ==
              row.get("statement_sha256"),
              "theorem statement hash does not bind to full source: " + name)
        axioms = row.get("transitive_axioms")
        check(isinstance(axioms, list) and
              set(axioms) <= {"propext", "Classical.choice", "Quot.sound"},
              "unreviewed transitive theorem axiom: " + name)
        check(row.get("compiler_result") == "PASS" and
              row.get("compiler_check") == "research",
              "theorem not established by source-bound Research Lean CI")
        verified.add(name)
    for row in negatives:
        check(isinstance(row, dict), "malformed semantic-negative receipt")
        path = secure_path(row.get("test_path", ""))
        check(path.is_file() and path.suffix == ".py" and
              path.name.startswith("test_") and
              digest(path) == row.get("source_sha256"),
              "negative test is missing, stale or not a test module")
        check(row.get("head_sha") == source_head and
              row.get("outcome") == "REJECTED_SEMANTIC",
              "negative mutant not explicitly rejected as a false theorem")
        name = row.get("test_name")
        check(isinstance(name, str) and
              re.search(r"(?m)^\s*def\s+" + re.escape(name) + r"\(",
                        path.read_text(encoding="utf-8")) is not None,
              "named negative test absent from bound source")
        log_path = row.get("log_path", "")
        log_file = secure_path(log_path)
        check(log_file.is_file() and digest(log_file) == row.get("log_sha256"),
              "negative test has no independently retained exact diagnostic log")
        diagnostics = log_file.read_text(encoding="utf-8", errors="replace").lower()
        check(("type mismatch" in diagnostics or
               "unsolved goals" in diagnostics or
               "application type mismatch" in diagnostics) and
              not any(x in diagnostics for x in
                      ("unknown module", "failed to import",
                       "parser error", "out of memory", "timed out")),
              "negative test passed for an invalid/non-semantic failure")
    return verified


def strict(receipts: dict, scope: str, manifest: dict | None,
           *, bundle_path: Path | str | None = None) -> dict:
    """Calculate EFFECTIVE reviewed cases/claims; never trust source JSON flags.

    The detached bundle is an external post-freeze artifact. Real signed
    GitHub check runs and independently authored exact-H review scopes are
    authenticated anew against live GitHub and local genuine Git objects.
    """
    summary = audit()
    check(scope in {"full45-strict", "scoped-release-strict"},
          "unknown strict acceptance scope")
    check(isinstance(receipts, dict) and
          receipts.get("format") == DETACHED_FORMAT,
          "canonical detached receipt v2 required; old flags cannot promote")
    check(receipts.get("phase") == "postmerge_acceptance",
          "postmerge strict acceptance requires actual M")
    try:
        provenance = verify_merged_v2(receipts)
        external = bundle_path or receipts.get("evidence_bundle_path")
        check(bool(external), "missing external immutable diagnostic bundle")
        members = load_detached_bundle(external,
                                       receipts.get("evidence_bundle_sha256"))
        decisions = read_json(NEW / "acceptance_decisions.json")
        inventory = read_json(NEW / "claim_inventory.json")
        result = effective_acceptance(
            receipts, head=provenance["H"], case_ledger=decisions,
            claims=inventory["claims"], members=members,
            accepted_checks=provenance["checks"],
            approved_review_scopes=provenance["review_scopes"])
    except (AuthenticationError, EvidenceError, OSError) as exc:
        raise GateError(str(exc)) from exc

    if scope == "full45-strict":
        check(result["accepted_case_count"] == 45 and
              result["pending_case_count"] == 0,
              "full45 still has unaccepted original case(s)")
    else:
        check(isinstance(manifest, dict) and
              manifest.get("status") == "APPROVED_SOURCE_BOUND",
              "scoped paper is not genuinely accepted")
        check(manifest.get("source_commit_sha") == provenance["M"],
              "paper manifest is not bound to the real merged M")
        claim_ids = manifest.get("claims", [])
        approved = manifest.get("approved_manuscript_claims", [])
        check(isinstance(claim_ids, list) and bool(claim_ids) and
              len(claim_ids) == len(set(claim_ids)) and
              claim_ids == approved and
              set(claim_ids) <= set(result["effective_claims"]),
              "manuscript uses unreviewed or missing claim")
        cross = read_json(NEW / "theorem_crosswalk.json")
        owners = {r["id"]: r for r in cross["closure_additions"]}
        proof_rows = receipts.get("compiler_axiom_receipts", [])
        for cid in claim_ids:
            check(cid in owners and
                  any(cid in row.get("claim_ids", []) and
                      row.get("path") == owners[cid]["path"]
                      for row in proof_rows),
                  "claim source owner not bound: " + cid)
        # Manuscript and PDF approval are independent of source CI. The
        # approved PDF's literal checksum must appear in a genuine exact-H
        # non-author review body, not just in a caller's self-assertion.
        pdf_hash = manifest.get("pdf_sha256")
        check(isinstance(pdf_hash, str) and SHA256.fullmatch(pdf_hash),
              "approved paper PDF checksum absent")
        check(any(s.get("pdf_sha256") == pdf_hash and
                  s.get("manuscript_approved") is True
                  for s in provenance["review_scopes"].values()),
              "independent scholarly PDF scope/byte review absent")
        check(bool(manifest.get("accepted_claim_receipts")) and
              bool(manifest.get("scientific_limitations")) and
              manifest.get("empirical_identification_status") == "NOT_ESTABLISHED",
              "claim/limitation boundaries missing or empirical proof invented")
    return {**summary, **result, "strict": scope,
            "source": provenance["M"], "frozen_head": provenance["H"]}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=("audit", "full45-strict",
                                      "scoped-release-strict"), default="audit")
    ap.add_argument("--receipts", type=Path)
    ap.add_argument("--manifest", type=Path)
    ap.add_argument("--bundle", type=Path,
                    help="externally retained hash-bound exact-H diagnostic archive")
    args = ap.parse_args(argv)
    try:
        if args.mode == "audit":
            out = audit()
        else:
            check(args.receipts is not None, "strict mode requires authenticated receipts")
            receipts = read_json(args.receipts)
            manifest = read_json(args.manifest) if args.manifest else None
            out = strict(receipts, args.mode, manifest, bundle_path=args.bundle)
    except (GateError, EvidenceError, KeyError, OSError, ValueError) as exc:
        print(f"NOT ACCEPTED: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
