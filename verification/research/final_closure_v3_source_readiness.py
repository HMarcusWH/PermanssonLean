"""Full PR113 v3 candidate type, source, route and producer validation.

This checker returns only source-evidence readiness, NEVER case/claim approval.
It is invoked *after* all 21 real GitHub producer ZIPs are reauthenticated.
A mathematically unrelated, successfully compiled test is not a valid original
COMPILER_SOURCE/EXACT_CHECK or SEMANTIC_NEGATIVE route.
"""
from __future__ import annotations

from final_closure_case_receipts import (
    EvidenceError, validate_compiler_receipt, validate_test_receipt,
)

CLAIMS = frozenset(("Q1", "Q2", "Q3", "M1", "M2", "M3",
                    "N1", "N2", "N3", "D8", "D9"))
POSITIVE_ROLES = frozenset(("COMPILER_SOURCE", "EXACT_CHECK"))


def need(condition, message):
    if not condition:
        raise EvidenceError(message)


def indexed(rows, kind):
    need(isinstance(rows, list) and all(isinstance(x, dict) for x in rows),
         "invalid " + kind + " rows")
    result = {}
    for row in rows:
        key = row.get("id")
        need(isinstance(key, str) and key and key not in result,
             "duplicate or missing " + kind + " id")
        result[key] = row
    return result


def supports_identity(row, required):
    """Full source path + qualified Lean declaration, not an owner label."""
    path, name = required.get("path"), required.get("declaration")
    if name is None:
        name = required.get("name")
        return (isinstance(name, str) and row.get("path") == path and
                (row.get("declaration") == name or
                 str(row.get("declaration", "")).endswith("." + name)))
    return (isinstance(name, str) and
            row.get("path") == path and row.get("declaration") == name)


def _original_roles(case):
    routes = case.get("test_method_candidates")
    need(isinstance(routes, list) and routes,
         "original method registry unavailable: " + str(case.get("case_id")))
    lookup = {}
    for row in routes:
        need(isinstance(row, dict) and
             row.get("role") in (POSITIVE_ROLES | {"SEMANTIC_NEGATIVE"}) and
             isinstance(row.get("path"), str) and
             isinstance(row.get("method"), str),
             "invalid original case method/role registry")
        key = (row["path"], row["method"])
        need(key not in lookup or lookup[key] == row["role"],
             "ambiguous original method role: " + str(case.get("case_id")))
        lookup[key] = row["role"]
    return lookup


def route_coverage(overlay, original_map, claim_map):
    """Require declared route roles/required theorem pairs, not ID intersections.

    Call only AFTER all proof/test source bytes and true GitHub producer jobs
    have passed validate_compiler_receipt / validate_test_receipt.
    """
    cases = original_map.get("cases") if isinstance(original_map, dict) else None
    claims = claim_map.get("claims") if isinstance(claim_map, dict) else None
    need(isinstance(cases, list) and len(cases) == 45 and
         isinstance(claims, list) and len(claims) == 11,
         "original 45 case/11 claim contract unavailable")
    bycase = {case["case_id"]: case for case in cases}
    byclaim = {claim["claim_id"]: claim for claim in claims}
    need(len(bycase) == 45 and set(byclaim) == CLAIMS,
         "duplicate or changed acceptance owners")
    proofs = indexed(overlay.get("compiler_axiom_receipts"), "proof")
    positives = indexed(overlay.get("positive_test_receipts"), "positive")
    negatives = indexed(overlay.get("semantic_negative_receipts"), "negative")
    need(len(proofs) == 259, "not all 259 source-owned Lean declarations supplied")
    cp, cn, qp, qn, wrong_roles, wrong_claim_sources, missing_support = (
        set(), set(), set(), set(), [], [], [])
    for cid, original in sorted(bycase.items()):
        applicable = [row for row in proofs.values()
                      if cid in row.get("case_ids", ())]
        required = original.get("historical_proof_declarations")
        need(isinstance(required, list) and required,
             "original case lacks genuine theorem requirements: " + cid)
        if (not all(any(supports_identity(row, req) for row in applicable)
                    for req in required) or
            not all(any(row.get("path") == link.get("path") for row in applicable)
                    for link in original.get("new_claim_source_candidates", ()))):
            missing_support.append(cid)
        roles = _original_roles(original)
        attached_plus = [row for row in positives.values()
                         if cid in row.get("case_ids", ())]
        attached_minus = [row for row in negatives.values()
                          if cid in row.get("case_ids", ())]
        correct_plus = [
            row for row in attached_plus
            if roles.get((row.get("test_path"), row.get("test_name")))
               in POSITIVE_ROLES]
        correct_minus = [
            row for row in attached_minus
            if roles.get((row.get("test_path"), row.get("test_name"))) ==
               "SEMANTIC_NEGATIVE"]
        if correct_plus: cp.add(cid)
        if correct_minus: cn.add(cid)
        if (attached_plus and not correct_plus) or (attached_minus and not correct_minus):
            wrong_roles.append(cid)
    for cid, original in sorted(byclaim.items()):
        attached = [row for row in proofs.values()
                    if cid in row.get("claim_ids", ())]
        required = original.get("declarations")
        need(isinstance(required, list) and required,
             "new claim missing full declaration list: " + cid)
        if not all(any(supports_identity(row, req) for row in attached)
                   for req in required):
            missing_support.append(cid)
        sources = original.get("test_source_candidates")
        need(isinstance(sources, list) and sources and
             len(sources) == len(set(sources)),
             "new claim missing registered test source paths: " + cid)
        plus = [row for row in positives.values()
                if cid in row.get("claim_ids", ())]
        minus = [row for row in negatives.values()
                 if cid in row.get("claim_ids", ())]
        if any(row.get("test_path") in sources for row in plus): qp.add(cid)
        if any(row.get("test_path") in sources for row in minus): qn.add(cid)
        if ((plus and cid not in qp) or (minus and cid not in qn)):
            wrong_claim_sources.append(cid)
    required_cases = set(bycase)
    result = {
        "format":"Permansson.PR113.V3RoleCoverage.v1",
        "cases_with_admissible_positive":len(cp),
        "cases_with_admissible_negative":len(cn),
        "claims_with_source_selected_positive":len(qp),
        "claims_with_source_selected_negative":len(qn),
        "missing_original_positive":sorted(required_cases - cp),
        "missing_original_semantic_negative":sorted(required_cases - cn),
        "missing_claim_positive":sorted(CLAIMS - qp),
        "missing_claim_semantic_negative":sorted(CLAIMS - qn),
        "missing_required_declaration_or_source":sorted(set(missing_support)),
        "inadmissible_original_method_roles":sorted(set(wrong_roles)),
        "inadmissible_claim_test_sources":sorted(set(wrong_claim_sources)),
        "independent_review":False,
        "mathematical_release_approved":False,
    }
    result["all_original_roles_and_claim_sources_complete"] = (
        len(cp) == len(cn) == 45 and len(qp) == len(qn) == 11 and
        not missing_support and not wrong_roles and not wrong_claim_sources)
    return result


def revalidate_source_receipts(overlay, head, members, accepted_checks,
                               producer_record, original_map, claim_map):
    """Real positive/negative compiler results, source hashes and job ZIP bytes."""
    need(producer_record.get("producer_count") == 21 and
         producer_record.get("status") == "REAL_PRODUCING_BYTES_UNREVIEWED" and
         producer_record.get("head_sha") == head,
         "actual 21 verified producer jobs are not available")
    proofs = indexed(overlay.get("compiler_axiom_receipts"), "proof")
    positives = indexed(overlay.get("positive_test_receipts"), "positive")
    negatives = indexed(overlay.get("semantic_negative_receipts"), "negative")
    need(len(proofs) == 259 and
         {row.get("id") for row in proofs.values()} ==
         {f"all:{n:04}" for n in range(259)},
         "canonical complete 259-case compiler indices are not retained")
    case_ids = {x.get("case_id") for x in original_map.get("cases", ())}
    need(len(case_ids) == 45, "original criterion identity changed")
    owners = {x for row in proofs.values() for x in row.get("case_ids", ())}
    claims = {x for row in proofs.values() for x in row.get("claim_ids", ())}
    need(owners == case_ids and claims == CLAIMS,
         "all 45/11 source proof owner coverage not authentic")
    for row in proofs.values():
        validate_compiler_receipt(
            row, head, members, accepted_checks, producer_record=producer_record)
    for row in positives.values():
        validate_test_receipt(
            row, head, members, accepted_checks,
            negative=False, producer_record=producer_record)
    for row in negatives.values():
        validate_test_receipt(
            row, head, members, accepted_checks,
            negative=True, producer_record=producer_record)
    return route_coverage(overlay, original_map, claim_map)
