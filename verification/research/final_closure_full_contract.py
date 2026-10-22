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
                        claims: list[dict]) -> dict:
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
