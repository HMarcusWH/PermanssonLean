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
from final_closure_authenticate import verify_source, AuthenticationError
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
        if row["decision"] in VERIFIED:
            check(bool(row.get("proof_declarations") and
                       row.get("positive_tests") and row.get("negative_tests") and
                       row.get("ci_receipts") and row.get("review_receipts")),
                  f"unearned accepted case: {cid}")
        else:
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


def strict(receipts: dict, scope: str, manifest: dict | None) -> dict:
    summary = audit()
    # Caller-supplied 'authenticated': true cannot promote a receipt.
    try:
        verify_source(receipts)
    except AuthenticationError as exc:
        raise GateError(str(exc)) from exc
    b, h, s, m = (receipts.get(k) for k in
                  ("base_sha", "head_sha", "synthetic_sha", "merged_main_sha"))
    for label, value in (("B", b), ("H", h), ("S", s), ("M", m)):
        check(isinstance(value, str) and bool(SHA40.fullmatch(value)),
              f"missing real {label} Git object")
    check(b == BASE, "wrong base for final build")
    check(bool(receipts.get("actual_synthetic_parents") == [b, h]),
          "synthetic merge parent order not established")
    check(bool(receipts.get("actual_merged_parents") == [b, h]) or
          bool(receipts.get("verified_rebased_merge_parent_chain")),
          "merged main parent evidence absent")
    check(receipts.get("merged_tree_sha") == receipts.get("synthetic_tree_sha") and
          bool(receipts.get("merged_tree_sha")), "different integrated trees")
    check(bool(receipts.get("source_bound_ci") and
               receipts.get("compiler_axiom_receipts") and
               receipts.get("semantic_negative_receipts") and
               receipts.get("independent_source_reviews")),
          "missing source-bound theorem/CI/review evidence")
    check(receipts.get("trusted_axioms") ==
          ["Classical.choice", "Quot.sound", "propext"],
          "unexpected or omitted trusted axiom")
    actually_verified = verify_claim_source_receipts(receipts, h)
    if scope == "full45-strict":
        check(summary["pending"] == 0, "at least one original case still pending")
    else:
        check(manifest is not None, "missing scoped-release manifest")
        check(manifest.get("status") == "APPROVED_SOURCE_BOUND",
              "release is a draft, not independently accepted")
        check(manifest.get("source_commit_sha") == m,
              "paper manifest does not bind final merged source")
        claims = manifest.get("claims", [])
        approved = manifest.get("approved_manuscript_claims", [])
        check(bool(claims) and claims == approved,
              "manuscript claim inventory mismatch")
        inventory = read_json(NEW / "claim_inventory.json")
        scoped = read_json(NEW / "theorem_crosswalk.json")
        accepted = {c["id"] for c in inventory["claims"]
                    if c.get("accepted") is True}
        crosswalk = {c["id"]: c for c in scoped["closure_additions"]}
        check(set(claims) <= accepted and set(claims) <= crosswalk.keys(),
              "manuscript cites unaccepted or unknown theorem claims")
        for cid in claims:
            source = crosswalk[cid]
            path = secure_path(source["path"])
            check(source.get("status") == "VERIFIED_SELECTED_SCOPE" and
                  path.is_file() and digest(path) == source.get("source_sha256"),
                  "accepted paper claim not tied to actual accepted source: " + cid)
            declarations = source.get("actual_declarations", [])
            check(declarations and all(name in actually_verified
                                       for name in declarations),
                  "claimed theorem not compiled and checked: " + cid)
        check(bool(manifest.get("accepted_claim_receipts") and
                   manifest.get("scientific_limitations") and
                   manifest.get("empirical_identification_status")),
              "missing claim certificates or scientific limits")
        check(bool(receipts.get("manuscript_review") and
                   receipts.get("pdf_visual_inspection")),
              "missing manuscript/PDF review")
    return {**summary, "strict": scope, "source": m}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=("audit", "full45-strict",
                                      "scoped-release-strict"), default="audit")
    ap.add_argument("--receipts", type=Path)
    ap.add_argument("--manifest", type=Path)
    args = ap.parse_args(argv)
    try:
        if args.mode == "audit":
            out = audit()
        else:
            check(args.receipts is not None, "strict mode requires authenticated receipts")
            receipts = read_json(args.receipts)
            manifest = read_json(args.manifest) if args.manifest else None
            out = strict(receipts, args.mode, manifest)
    except (GateError, KeyError, OSError, ValueError) as exc:
        print(f"NOT ACCEPTED: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
