"""Strict, source-bound independent security review for the *versioned* T2/A2.

This replaces only the proposed v2/v3 review intake; the frozen v1 original
and historical T interpreter are never mutated. No synthetic review or
source-embedded status becomes reviewer authority.
"""
from __future__ import annotations

import re
from final_closure_authenticate import current_reviews_by_user
from infrastructure_acceptance import (
    AUTHORITY_PATH, REVIEW_PREFIX, InfrastructureError,
    exact_committed_blob,
)
from pr113_boundary_io import strict_json_object
from release_target import B113

SHA = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
CLAIMED = frozenset(("head_sha", "workflow_sha256", "T_artifact_sha256",
                     "A2_artifact_sha256", "original_base_sha"))


def need(ok, reason):
    if not ok:
        raise InfrastructureError(reason)


def authority_policy(head, *, git):
    """Read the exact committed policy; reject duplicated JSON authority."""
    need(isinstance(head, str) and SHA.fullmatch(head),
         "security reviewer policy requires genuine exact H")
    try:
        raw = exact_committed_blob(head, AUTHORITY_PATH, git=git)
        policy = strict_json_object(raw, max_bytes=64*1024)
    except (TypeError, OSError, ValueError) as exc:
        raise InfrastructureError(
            "independent reviewer roster absent or contains ambiguous JSON") from exc
    need(isinstance(policy, dict) and
         set(policy) == {"format", "status", "owner", "reviewers"}
         and policy.get("format") == "Permansson.InfrastructureReviewerAuthority.v1"
         and policy.get("status") == "OWNER_AUTHORIZED"
         and policy.get("owner") == "HMarcusWH"
         and type(policy.get("reviewers")) is list
         and bool(policy["reviewers"]),
         "independent reviewer not separately owner-authorized")
    return policy


def approved_security_review(review_id, author, head, attest, policy, *,
                             paginate):
    """Require a live, latest, nonauthor GitHub PR review on exact H/T2/A2."""
    need(type(review_id) is int and review_id > 0
         and type(author) is str and bool(author)
         and type(head) is str and SHA.fullmatch(head),
         "original security review identity or head is missing")
    need(type(attest) is dict and set(attest) == CLAIMED
         and attest["head_sha"] == head
         and attest["original_base_sha"] == B113
         and all(type(attest[k]) is str and SHA256.fullmatch(attest[k])
                 for k in ("workflow_sha256", "T_artifact_sha256",
                           "A2_artifact_sha256")),
         "security review contract is not exact H/workflow/T/A2 source")
    need(type(policy) is dict and
         policy.get("format") == "Permansson.InfrastructureReviewerAuthority.v1"
         and policy.get("status") == "OWNER_AUTHORIZED"
         and policy.get("owner") == "HMarcusWH"
         and type(policy.get("reviewers")) is list
         and bool(policy["reviewers"]),
         "security reviewer roster has not been owner-authorized")
    rows = paginate("/pulls/113/reviews")
    need(type(rows) is list, "genuine GitHub review source absent")
    latest = current_reviews_by_user(rows)
    matching = []
    for review in latest.values():
        if not isinstance(review, dict) or review.get("id") != review_id:
            continue
        login = (review.get("user") or {}).get("login")
        need(type(login) is str and login != author
             and review.get("commit_id") == head
             and review.get("state") == "APPROVED"
             and type(review.get("submitted_at")) is str
             and bool(review["submitted_at"]),
             "current exact-H security review is absent, dismissed or self-authored")
        roster = [entry for entry in policy["reviewers"]
                  if type(entry) is dict
                  and entry.get("login") == login
                  and entry.get("approved_by") == "HMarcusWH"
                  and entry.get("independence_disclosed") is True]
        need(len(roster) == 1,
             "review author lacks a unique approved independent reviewer role")
        body = review.get("body")
        need(type(body) is str and 0 < len(body.encode("utf-8")) <= 64*1024,
             "missing or unbounded original reviewer attestation")
        declarations = [line.strip()[len(REVIEW_PREFIX):].strip()
                        for line in body.splitlines()
                        if line.strip().startswith(REVIEW_PREFIX)]
        need(len(declarations) == 1,
             "security reviewer attestation absent or ambiguous")
        try:
            record = strict_json_object(declarations[0].encode("utf-8"),
                                        max_bytes=64*1024)
        except (ValueError, TypeError) as exc:
            raise InfrastructureError(
                "duplicate, noncanonical or invalid security review JSON") from exc
        need(type(record) is dict and set(record) == CLAIMED
             and record == attest,
             "independent reviewer did not approve exact T/H/A2 artifact SHA")
        matching.append(review["id"])
    need(matching == [review_id],
         "genuine latest independent exact-H security approval missing")
    return True
