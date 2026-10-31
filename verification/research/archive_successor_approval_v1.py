"""Owner-approved installed workflow changes from the archive successor policy.

The PR #113 staged-migration checks require the 25 installed workflows to be
the original preactivation bytes. The owner-engineering archive successor
contract v1 changes one of them, `research-integrity.yml`, in a recorded way.
Those checks call this module, with the committed policy bytes read at the
head they inspect, to accept exactly that change: from exactly its original
preactivation blob to exactly the approved blob. Any other difference is still
a silent alteration.

Standard library only, so it can be imported wherever the staged checks run.
This is an owner engineering decision, not an independent security review.
"""
from __future__ import annotations

import json
import re

POLICY_PATH = "verification/research/archive_successor_policy_v1.json"
FORMAT = "Permansson.ArchiveSuccessor.OwnerEngineeringPolicy.v1"
PREACTIVATION_25_HEAD = "5189f0c4a0db7535d57a9ff2a7aef6a3e76191b6"
WORKFLOW = ".github/workflows/research-integrity.yml"
SHA40 = re.compile(r"^[0-9a-f]{40}$")


class ApprovalError(ValueError):
    pass


def _unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ApprovalError("duplicate key in archive successor policy: " + key)
        result[key] = value
    return result


def approved_workflow_changes(raw: bytes) -> dict[str, tuple[str, str]]:
    """{workflow file name: (preactivation blob, approved blob)}; exactly one entry."""
    try:
        policy = json.loads(raw.decode("utf-8"), object_pairs_hook=_unique)
    except (UnicodeError, ValueError) as exc:
        raise ApprovalError("archive successor policy is not strict JSON") from exc
    rows = policy.get("approved_workflow_changes") if isinstance(policy, dict) else None
    if not (isinstance(policy, dict) and policy.get("format") == FORMAT
            and policy.get("authority") == "OWNER_ENGINEERING_POLICY"
            and policy.get("independent_security_review") is False
            and policy.get("preactivation_25_head") == PREACTIVATION_25_HEAD
            and isinstance(rows, list) and len(rows) == 1 and isinstance(rows[0], dict)
            and set(rows[0]) == {"path", "preactivation_blob", "approved_blob"}
            and rows[0]["path"] == WORKFLOW
            and all(isinstance(rows[0][k], str) and SHA40.fullmatch(rows[0][k])
                    for k in ("preactivation_blob", "approved_blob"))
            and rows[0]["preactivation_blob"] != rows[0]["approved_blob"]):
        raise ApprovalError("archive successor policy does not describe one owner-approved workflow change")
    return {WORKFLOW.removeprefix(".github/workflows/"): (rows[0]["preactivation_blob"], rows[0]["approved_blob"])}
