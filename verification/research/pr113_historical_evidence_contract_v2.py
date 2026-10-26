"""Strict nonauthorizing PR113 v2 historical T/T2 and A2 envelope contract.

V1 required a completed 12-check set; a v2 historical-only producer must
instead bind its TWO real source artifacts without circularly requiring
the very Research/Archive jobs that consume them. The later aggregate
requires the exact 12 source-bound CI contexts.

Structure and source intent here are not authentication: consumers must
still verify live GitHub jobs/artifacts, true Git objects, and independent
review through the existing gates.
"""
from __future__ import annotations

import json

from final_closure_authenticate import REQUIRED
from infrastructure_acceptance import InfrastructureError
from release_target import candidate_bindings

FORMAT = "Permansson.PR113.InfrastructureEvidence.v2"
FIELDS = frozenset({
    "format", "target", "source_bound_ci", "historical_T",
    "historical_A2", "security_review_id",
})
ARTIFACT_FIELDS = frozenset({
    "run_id", "run_attempt", "job_id", "check_run_id", "artifact_id",
})
CHECK_FIELDS = frozenset({"name", "id", "head_sha"})
MAX_BYTES = 64 * 1024


class InfrastructureEnvelopeError(InfrastructureError):
    pass


def need(value, message):
    if not value:
        raise InfrastructureEnvelopeError(message)


def strictly_positive(value):
    """bool is a subclass of int in Python, but never an API ID."""
    return type(value) is int and value > 0


def validate_envelope(payload, *, require_all_checks=False):
    """Validate external v2 structure; leave every approval decision false.

    A historical-only check may read an empty CI list or a complete
    aggregate without treating the list as authenticated. Only the real
    aggregate gate authenticates all twelve live checks, and it invokes
    this validator with require_all_checks=True.
    """
    need(isinstance(payload, dict) and set(payload) == FIELDS
         and payload.get("format") == FORMAT,
         "unknown/malformed versioned historical evidence envelope")
    target = payload.get("target")
    try:
        candidate_bindings(target)
    except (TypeError, ValueError) as exc:
        raise InfrastructureEnvelopeError(
            "wrong or unbound historical evidence source target") from exc
    need(target["phase"] == "infrastructure_premerge",
         "certification successor cannot borrow PR113 historical evidence")
    need(strictly_positive(payload.get("security_review_id")),
         "historical evidence requires genuine review ID placeholder, not approval")
    records = {}
    for name in ("historical_T", "historical_A2"):
        rec = payload.get(name)
        need(isinstance(rec, dict) and set(rec) == ARTIFACT_FIELDS
             and all(strictly_positive(rec.get(key))
                     for key in ARTIFACT_FIELDS),
             "invalid v2 historical run/job/check/artifact identity: " + name)
        records[name] = rec
    t, a = records["historical_T"], records["historical_A2"]
    need(t["run_id"] == a["run_id"]
         and t["run_attempt"] == a["run_attempt"]
         and t["job_id"] != a["job_id"]
         and t["check_run_id"] != a["check_run_id"]
         and t["artifact_id"] != a["artifact_id"],
         "historical T and A2 must be distinct jobs/artifacts in the same run attempt")

    checks = payload.get("source_bound_ci")
    need(isinstance(checks, list)
         and len(checks) in (0, len(REQUIRED)),
         "historical input must have zero or all twelve declared CI contexts")
    if require_all_checks:
        need(len(checks) == len(REQUIRED),
             "aggregate infrastructure report needs twelve CI contexts")
    if checks:
        names, ids = [], []
        for row in checks:
            need(isinstance(row, dict) and set(row) == CHECK_FIELDS
                 and isinstance(row.get("name"), str)
                 and row["name"] in REQUIRED
                 and strictly_positive(row.get("id"))
                 and row.get("head_sha") == target["head_sha"],
                 "foreign, malformed or stale historical CI identity")
            names.append(row["name"])
            ids.append(row["id"])
        need(len(names) == len(set(names))
             and set(names) == REQUIRED
             and len(ids) == len(set(ids)),
             "missing/repeated source CI context or borrowed check-run ID")
    return payload


def parse_envelope(raw, *, require_all_checks=False):
    """Bound raw JSON and reject duplicate keys before any network or Git read."""
    need(type(raw) is bytes and 0 < len(raw) <= MAX_BYTES,
         "v2 historical envelope bytes missing or unbounded")

    def no_duplicate_keys(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise InfrastructureEnvelopeError(
                    "duplicate historical evidence JSON key: " + key)
            result[key] = value
        return result

    try:
        value = json.loads(raw, object_pairs_hook=no_duplicate_keys)
    except (UnicodeError, ValueError, TypeError) as exc:
        raise InfrastructureEnvelopeError(
            "malformed/ambiguous historical evidence JSON") from exc
    return validate_envelope(value, require_all_checks=require_all_checks)
