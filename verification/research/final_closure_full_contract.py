"""Exact 45-case AND 11-claim selected-source conjunction.

This module checks EFFECTIVE decisions issued by the authenticated gate,
not historic candidate counts, hand-authored owner labels, or CI green flags.
It is required before an exact-H source can be called full-source ready.
"""
from __future__ import annotations

from final_closure_case_receipts import EvidenceError

ORIGINAL_CLAIMS = frozenset((
    "Q1", "Q2", "Q3", "M1", "M2", "M3",
    "N1", "N2", "N3", "D8", "D9",
))
VERIFIED = frozenset(("VERIFIED_SELECTED_SCOPE", "VERIFIED_NEGATIVE"))


def require_full_source(result: dict, case_ledger: dict,
                        claims: list[dict], case_map: dict) -> dict:
    """Fail closed on missing, duplicated or spurious EFFECTIVE requirements."""
    if not isinstance(result, dict) or not isinstance(case_ledger, dict) or \
       not isinstance(claims, list):
        raise EvidenceError("full source evidence has invalid types")
    cases = case_ledger.get("cases")
    if not isinstance(cases, list) or len(cases) != 45 or \
       any(not isinstance(row, dict) for row in cases):
        raise EvidenceError("full source must preserve all 45 original rows")
    originals = [row.get("case_id") for row in cases]
    if len(set(originals)) != 45 or any(not isinstance(x, str) for x in originals):
        raise EvidenceError("original case identifiers are not unique")
    claim_ids = [row.get("id") for row in claims if isinstance(row, dict)]
    if len(claim_ids) != 11 or len(set(claim_ids)) != 11 or \
       set(claim_ids) != ORIGINAL_CLAIMS:
        raise EvidenceError("canonical eleven claims are missing or substituted")

    # An accepted count is meaningless while any original case still lacks an
    # explicit current-source test selection. Source maps are tracked at H and
    # reviewed with H; historical aliases alone are not execution receipts.
    selected = case_map.get("cases") if isinstance(case_map, dict) else None
    if not isinstance(selected, list) or len(selected) != 45 or \
       any(not isinstance(row, dict) for row in selected):
        raise EvidenceError("frozen case-to-test mapping is missing")
    selection = [row.get("case_id") for row in selected]
    if len(set(selection)) != 45 or set(selection) != set(originals):
        raise EvidenceError("case-to-test mapping is incomplete or altered")
    for row in selected:
        tests = row.get("test_source_candidates")
        if (not isinstance(tests, list) or not tests or
            len(set(tests)) != len(tests) or
            not all(isinstance(t, str) and
                    t.startswith("verification/research/test_") and
                    t.endswith(".py") for t in tests)):
            raise EvidenceError(
                "original case lacks an explicit selected test: " + row["case_id"])
        if not row.get("historical_proof_declarations"):
            raise EvidenceError("original case lacks proof route: " + row["case_id"])

    effective_cases = result.get("effective_cases")
    effective_claims = result.get("effective_claims")
    if not isinstance(effective_cases, dict) or \
       set(effective_cases) != set(originals) or \
       any(status not in VERIFIED for status in effective_cases.values()) or \
       result.get("accepted_case_count") != 45 or \
       result.get("pending_case_count") != 0:
        raise EvidenceError("full selected source is missing accepted original cases")
    if not isinstance(effective_claims, list) or \
       len(effective_claims) != 11 or len(set(effective_claims)) != 11 or \
       set(effective_claims) != ORIGINAL_CLAIMS or \
       result.get("accepted_claim_count") != 11:
        raise EvidenceError("full selected source is missing an accepted claim")
    return {
        "status": "FULL_SELECTED_SOURCE_SCOPE_REVIEWED",
        "effective_case_count": 45,
        "effective_claim_count": 11,
        "case_ids": sorted(originals),
        "claim_ids": sorted(ORIGINAL_CLAIMS),
        "not_yet_release": True,
    }


def require_full_release(result: dict, case_ledger: dict, claims: list[dict],
                         case_map: dict, manifest: dict,
                         provenance: dict) -> dict:
    """Conjoin full math, scholarly PDF, real M and authenticated build/archive.

    Provenance MUST be built from external authenticated CI and scholarly
    attestations, not copied from caller-supplied manifest flags. At present
    authentication does not provide reproduction/archive evidence: until
    ENG-08 is wired, this gate intentionally remains closed.
    """
    import re
    source = require_full_source(result, case_ledger, claims, case_map)
    if not isinstance(manifest, dict) or not isinstance(provenance, dict):
        raise EvidenceError("full release lacks reviewed manuscript/provenance")
    merged = provenance.get("M")
    if not isinstance(merged, str) or not re.fullmatch(r"[0-9a-f]{40}", merged):
        raise EvidenceError("actual merged M is unavailable")
    if manifest.get("status") != "APPROVED_SOURCE_BOUND" or \
       manifest.get("source_commit_sha") != merged:
        raise EvidenceError("source-faithful approved M manuscript missing")
    published = manifest.get("claims")
    reviewed = manifest.get("approved_manuscript_claims")
    if not isinstance(published, list) or \
       published != reviewed or len(published) != 11 or \
       len(set(published)) != 11 or set(published) != ORIGINAL_CLAIMS:
        raise EvidenceError("paper is not approved for exactly all 11 claims")
    accepted = manifest.get("accepted_claim_receipts")
    if not isinstance(accepted, list) or len(accepted) != 11 or \
       any(not isinstance(r, dict) or
           not isinstance(r.get("claim_id"), str) or
           not re.fullmatch(r"[0-9a-f]{64}",
                            str(r.get("receipt_sha256", "")))
           for r in accepted) or \
       {r["claim_id"] for r in accepted} != ORIGINAL_CLAIMS:
        raise EvidenceError("full paper has incomplete accepted-claim receipts")
    pdf = manifest.get("pdf_sha256")
    pages = manifest.get("pdf_pages")
    if not isinstance(pdf, str) or not re.fullmatch(r"[0-9a-f]{64}", pdf) or \
       not isinstance(pages, dict) or not pages or \
       any(not re.fullmatch(r"page-[0-9]+[.]png", name) or
           not isinstance(dig, str) or
           not re.fullmatch(r"[0-9a-f]{64}", dig)
           for name, dig in pages.items()):
        raise EvidenceError("complete exact PDF page digests are missing")
    numbered = sorted(int(name[5:-4]) for name in pages)
    if numbered != list(range(1, len(pages)+1)):
        raise EvidenceError("full PDF pages are missing or duplicated")
    if manifest.get("pdf_page_count") != len(pages):
        raise EvidenceError("PDF page count does not match full render")
    if manifest.get("empirical_identification_status") != "NOT_ESTABLISHED" or \
       not manifest.get("scientific_limitations"):
        raise EvidenceError("paper has unsupported empirical or scope claims")
    reviews = provenance.get("scholarly_reviews", [])
    if not isinstance(reviews, list) or not any(
        isinstance(s, dict) and s.get("pdf_sha256") == pdf and
        s.get("pages") == pages and
        set(s.get("claim_ids", [])) == ORIGINAL_CLAIMS
        for s in reviews
    ):
        raise EvidenceError("independent exact-PDF review is missing")

    # The final artifact receipts are produced by an independent authenticator,
    # never by copying JSON values from the candidate release manifest.
    for label, kind in (("reproduction", "TWO_CLEAN_SOURCE_BUILDS"),
                        ("archive", "COMPLETE_ARCHIVE_REPLAY")):
        expected = manifest.get(label + "_evidence_sha256")
        signed = provenance.get(label + "_evidence")
        if (not isinstance(expected, str) or
            not re.fullmatch(r"[0-9a-f]{64}", expected) or
            not isinstance(signed, dict) or
            signed.get("status") != kind or
            signed.get("source_commit_sha") != merged or
            signed.get("pdf_sha256") != pdf or
            signed.get("artifact_sha256") != expected or
            signed.get("authenticated_ci_artifact") is not True):
            raise EvidenceError("authenticated " + label + " evidence missing")
    return {
        **source,
        "status": "FULL_MATHEMATICAL_CLOSURE_RELEASE_READY",
        "actual_merged_main_sha": merged,
        "pdf_sha256": pdf,
        "pdf_page_count": len(pages),
        "not_yet_release": False,
    }
