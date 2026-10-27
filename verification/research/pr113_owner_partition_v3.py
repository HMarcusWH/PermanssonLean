"""Typed structural inventory for the 45+20+11 original source owners.

One GitHub artifact ZIP may contain many owners. This validates only source
contract SHAPE and the exact claimed ownership partition. GitHub run, digest,
Lean execution and independent review remain separately mandatory.
"""
from __future__ import annotations

FORMAT = "Permansson.PR113.ControlProducerExtension.v3.1"
CLAIMS = frozenset(("Q1", "Q2", "Q3", "M1", "M2", "M3",
                    "N1", "N2", "N3", "D8", "D9"))
COUNTS = {"original_positive": 45, "legacy_negative": 20, "claim_pair": 11}


class OwnerPartitionError(ValueError):
    pass


def require(ok, message):
    if not ok:
        raise OwnerPartitionError(message)


def original_owner_artifacts(payload):
    """Return actual producer ARTIFACT IDs, never a fixed number of ZIPs."""
    require(type(payload) is dict and payload.get("format") == FORMAT
            and payload.get("source_controls_accepted") is False
            and payload.get("independent_security_review") is False
            and payload.get("mathematical_approval") is False,
            "full owner contract is malformed or self-approved")
    jobs = payload.get("producers")
    require(type(jobs) is list and 0 < len(jobs) <= 76,
            "missing or unbounded original owner-producing jobs")
    artifacts = set()
    by_kind = {key: set() for key in COUNTS}
    for job in jobs:
        require(type(job) is dict and
                type(job.get("artifact_id")) is int
                and job["artifact_id"] > 0
                and job["artifact_id"] not in artifacts,
                "duplicate or nonnumeric original CI artifact identity")
        artifacts.add(job["artifact_id"])
        owners = job.get("owners")
        require(type(owners) is list and bool(owners),
                "owner-producing artifact has no actual source owners")
        for owner in owners:
            require(type(owner) is dict
                    and type(owner.get("kind")) is str
                    and owner["kind"] in COUNTS
                    and type(owner.get("owner_id")) is str
                    and bool(owner["owner_id"])
                    and owner["owner_id"] not in by_kind[owner["kind"]],
                    "unknown, missing or repeated original owner identity")
            by_kind[owner["kind"]].add(owner["owner_id"])
    require(all(len(by_kind[k]) == n for k, n in COUNTS.items())
            and by_kind["legacy_negative"] <= by_kind["original_positive"]
            and by_kind["claim_pair"] == CLAIMS,
            "original source owners do not cover exactly 45+20+11")
    return sorted(artifacts)
