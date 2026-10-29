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
    FORMAT as DETACHED_FORMAT, FORMAT_V3 as DETACHED_V3, EvidenceError,
    load_detached_bundle, effective_acceptance,
)
from final_closure_schema import validate_overlay
from pr113_boundary_io import strict_json_object
from final_closure_full_contract import (
    require_preseal_release, require_full_release,
    require_complete_obligation_receipts,
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
    # Historical and current case/claim documents must not have
    # ambiguous JSON keys before the research audit uses their values.
    return strict_json_object(path.read_bytes(), max_bytes=8*1024*1024)


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
    """Legacy v1 proof-receipt API intentionally DISABLED for acceptance.

    The old source-name/digest and diagnostic text checks were insufficient
    for case-specific acceptance and external bundle provenance. Always use
    the read-only authenticated v2 strict() gate with exact head, CI, tested
    mutant bytes and independent scope review.
    """
    raise GateError(
        "legacy free-form proof receipt verification retired; "
        "use detached authenticated v2 receipt bundle and strict()")


def strict(receipts: dict, scope: str, manifest: dict | None,
           *, bundle_path: Path | str | None = None,
           reproduction_attachment: dict | None = None,
           postseal_attachment: dict | None = None,
           v31_attachment: dict | None = None) -> dict:
    """Calculate EFFECTIVE reviewed cases/claims; never trust source JSON flags.

    The detached bundle is an external post-freeze artifact. Real signed
    GitHub check runs and independently authored exact-H review scopes are
    authenticated anew against live GitHub and local genuine Git objects.
    """
    try:
        validate_overlay(receipts)
    except EvidenceError as exc:
        raise GateError(str(exc)) from exc
    summary = audit()
    check(scope in {"full45-strict", "scoped-release-strict",
                    "postmerge-preseal-strict", "full-release-strict"},
          "unknown strict acceptance scope")
    check(isinstance(receipts, dict) and
          receipts.get("format") in (DETACHED_FORMAT, DETACHED_V3),
          "canonical detached v2/v3 receipts required; old flags cannot promote")
    check(receipts.get("phase") == "postmerge_acceptance",
          "postmerge strict acceptance requires actual M")
    if scope in ("full45-strict", "postmerge-preseal-strict",
                 "full-release-strict"):
        check(receipts.get("format") == DETACHED_V3,
              "full 45/11 scope requires genuine producer-bound v3 receipts")
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

    # All 76 real source-owned positive/negative controls are mandatory for
    # either complete scholarly release mode. A legacy original-v3 only
    # source receipt cannot be promoted by successful review or green CI.
    additional_source = {}
    if scope in ("postmerge-preseal-strict", "full-release-strict"):
        from pr113_mandatory_v31 import (
            authenticate_all_76, MandatoryV31Error)
        check(isinstance(v31_attachment, dict) and
              set(v31_attachment) == {
                  "additional_contract", "additional_zips",
                  "workflow_blob_candidates"} and
              all(v31_attachment[name] is not None for name
                  in v31_attachment),
              "full scholarly release requires 76 original v3.1 source controls")
        try:
            additional_source = authenticate_all_76(
                provenance["H"], receipts, members, **v31_attachment)
        except (MandatoryV31Error, OSError, TypeError, ValueError) as exc:
            raise GateError(
                "real full-scope v3.1 producer evidence is missing: " +
                str(exc)) from exc
    full_result = {}
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
        # Scientific manuscript review happens AFTER real M and signed PDF
        # inspection. A postmerge non-author GitHub attestation must bind the
        # literal PDF, all rendered page hashes and the approved claim set.
        pdf_hash = manifest.get("pdf_sha256")
        pages = manifest.get("pdf_pages")
        check(isinstance(pdf_hash, str) and SHA256.fullmatch(pdf_hash) and
              isinstance(pages, dict) and bool(pages),
              "approved PDF checksum and complete page hashes absent")
        check(any(s.get("pdf_sha256") == pdf_hash and
                  s.get("pages") == pages and
                  set(s.get("claim_ids", [])) == set(claim_ids)
                  for s in provenance["scholarly_reviews"]),
              "postmerge independent manuscript/page review absent")
        check(bool(manifest.get("accepted_claim_receipts")) and
              bool(manifest.get("scientific_limitations")) and
              manifest.get("empirical_identification_status") == "NOT_ESTABLISHED",
              "claim/limitation boundaries missing or empirical proof invented")
    if scope in ("postmerge-preseal-strict", "full-release-strict"):
        # A claimed PDF/CI digest is NOT evidence. Authenticate the actual
        # successful merged-main producing job and its original ZIP bytes.
        if reproduction_attachment is not None:
            from final_closure_reproduction_auth import (
                authenticate_merged_reproduction,
                ReproductionAuthenticationError,
            )
            check(isinstance(reproduction_attachment, dict) and
                  set(reproduction_attachment) == {"identities", "zip_file"} and
                  isinstance(manifest, dict) and
                  isinstance(manifest.get("pdf_sha256"), str),
                  "untyped detached genuine reproduction input")
            try:
                reproduced = authenticate_merged_reproduction(
                    provenance["M"], manifest["pdf_sha256"],
                    reproduction_attachment["identities"],
                    Path(reproduction_attachment["zip_file"]))
            except (ReproductionAuthenticationError, OSError, KeyError) as exc:
                raise GateError("real merged source/PDF reproduction failed: " +
                                str(exc)) from exc
            provenance = {**provenance, "reproduction_evidence": reproduced}
        if scope == "full-release-strict" and postseal_attachment is not None:
            from final_closure_postseal_auth import (
                authenticate_postseal, PostsealAuthenticationError)
            check(isinstance(postseal_attachment, dict) and
                  set(postseal_attachment) == {"identities", "zip_file"} and
                  isinstance(manifest, dict) and
                  isinstance(manifest.get("pdf_sha256"), str),
                  "untyped detached genuine postseal evidence")
            try:
                archive = authenticate_postseal(
                    provenance["M"], manifest["pdf_sha256"],
                    postseal_attachment["identities"],
                    Path(postseal_attachment["zip_file"]))
            except (PostsealAuthenticationError, OSError, KeyError) as exc:
                raise GateError("genuine merged-M postseal authentication failed: "+
                                str(exc)) from exc
            provenance = {**provenance, "archive_evidence": archive}
        try:
            original_map = read_json(NEW / "acceptance_case_source_map.json")
            validator = (require_preseal_release
                         if scope == "postmerge-preseal-strict"
                         else require_full_release)
            full_result = validator(
                result, decisions, inventory["claims"],
                original_map, manifest, provenance)
            full_result.update(require_complete_obligation_receipts(
                receipts, original_map,
                read_json(NEW / "claim_declaration_map.json")))
        except EvidenceError as exc:
            raise GateError(str(exc)) from exc
    return {**summary, **result, **full_result,
            "additional_source_execution": additional_source,
            "strict": scope,
            "source": provenance["M"], "frozen_head": provenance["H"]}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=("audit", "full45-strict",
                                      "scoped-release-strict",
                                      "postmerge-preseal-strict",
                                      "full-release-strict"), default="audit")
    ap.add_argument("--receipts", type=Path)
    ap.add_argument("--manifest", type=Path)
    ap.add_argument("--bundle", type=Path,
                    help="externally retained hash-bound exact-H diagnostic archive")
    ap.add_argument("--reproduction-zip", type=Path,
                    help="original real merged-M clean-build Actions artifact ZIP")
    ap.add_argument("--reproduction-ids", type=Path,
                    help="detached source-bound GitHub run/job/check/artifact IDs")
    ap.add_argument("--postseal-zip", type=Path,
                    help="future independently authorized GH postseal artifact ZIP")
    ap.add_argument("--postseal-ids", type=Path,
                    help="real source-bound producing postseal job/check/artifact IDs")
    ap.add_argument("--additional-contract", type=Path)
    ap.add_argument("--additional-zips", type=Path)
    ap.add_argument("--workflow-blob-candidates", type=Path)
    args = ap.parse_args(argv)
    try:
        if args.mode == "audit":
            out = audit()
        else:
            check(args.receipts is not None, "strict mode requires authenticated receipts")
            receipts = read_json(args.receipts)
            manifest = read_json(args.manifest) if args.manifest else None
            check(bool(args.reproduction_zip) == bool(args.reproduction_ids),
                  "reproduction ZIP and exact GitHub identities must be paired")
            source = ({"zip_file": args.reproduction_zip,
                       "identities": read_json(args.reproduction_ids)}
                      if args.reproduction_zip else None)
            check(bool(args.postseal_zip) == bool(args.postseal_ids),
                  "postseal ZIP and exact GitHub producing IDs must be paired")
            replay = ({"zip_file":args.postseal_zip,
                       "identities":read_json(args.postseal_ids)}
                      if args.postseal_zip else None)
            v31 = ({
                "additional_contract": args.additional_contract,
                "additional_zips": args.additional_zips,
                "workflow_blob_candidates": args.workflow_blob_candidates}
                if any(x is not None for x in (
                    args.additional_contract, args.additional_zips,
                    args.workflow_blob_candidates)) else None)
            out = strict(receipts, args.mode, manifest,
                         bundle_path=args.bundle,
                         reproduction_attachment=source,
                         postseal_attachment=replay,
                         v31_attachment=v31)
    except (GateError, EvidenceError, KeyError, OSError, ValueError) as exc:
        print(f"NOT ACCEPTED: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
