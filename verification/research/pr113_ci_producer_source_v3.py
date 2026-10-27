"""Authenticate real PR113/CERT source-control workflow execution.

The dispatch branch, PR and source head must be live GitHub/Git identities;
inputs are hints only. This module never approves cases, claims or a release.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import sys

from pr113_boundary_io import strict_json_object
from pr113_producer_target_v3 import authenticated_producer_branch
from release_target import REPOSITORY

SHA = re.compile(r"^[0-9a-f]{40}$")
MODES = frozenset(("source_controls", "reviewed_legacy20"))
FORMAT = "Permansson.PR113.ActualOwnerProducerSource.v3"


class SourceDispatchError(ValueError):
    pass


def require(value, message):
    if not value:
        raise SourceDispatchError(message)


def authenticate(head, mode, *, env=None, event_data=None,
                 branch_check=authenticated_producer_branch):
    """Return a source-only receipt; current event, NOT static source labels."""
    env = os.environ if env is None else env
    require(isinstance(head, str) and bool(SHA.fullmatch(head))
            and mode in MODES
            and env.get("GITHUB_ACTIONS") == "true"
            and env.get("GITHUB_REPOSITORY") == REPOSITORY
            and env.get("GITHUB_SHA") == head,
            "genuine checked-out producer source event required")
    kind = env.get("GITHUB_EVENT_NAME")
    require(kind in ("push", "workflow_dispatch"),
            "owner controls require a branch push or explicit dispatch")
    if event_data is None:
        fp = Path(env.get("GITHUB_EVENT_PATH", ""))
        require(fp.is_file() and not fp.is_symlink()
                and 0 < fp.stat().st_size <= 8*1024*1024,
                "real GitHub producer event unavailable")
        event_data = fp.read_bytes()
    event = strict_json_object(event_data, max_bytes=8*1024*1024)
    require((event.get("repository") or {}).get("full_name") == REPOSITORY,
            "producer event targets foreign repository")
    hint = env.get("PERMANSSON_CERT_PR_NUMBER", "")
    if kind == "push":
        require(mode == "source_controls"
                and event.get("ref") == env.get("GITHUB_REF")
                and event.get("after") == head
                and env.get("GITHUB_REF") ==
                    "refs/heads/research/final-mathematical-closure"
                and not hint,
                "push is not original exact-H unreviewed producer source")
    else:
        inputs = event.get("inputs")
        require(isinstance(inputs, dict)
                and inputs.get("source_head") == head
                and inputs.get("run_mode") == mode
                and inputs.get("cert_pr_number", "") == hint
                and env.get("PR113_REQUESTED_SOURCE_HEAD") == head
                and env.get("PR113_REQUESTED_RUN_MODE") == mode,
                "workflow dispatch is not bound to original source/mode/input")
    try:
        branch = branch_check(head, env=env)
    except (ValueError, TypeError, KeyError) as exc:
        raise SourceDispatchError("producer branch/PR failed live verification") from exc
    require(env.get("GITHUB_REF") == "refs/heads/" + branch,
            "authenticated producer branch differs from actual GitHub ref")
    return {
        "format": FORMAT,
        "status": "AUTHENTIC_GITHUB_PRODUCER_SOURCE_NOT_REVIEWED",
        "head_sha": head,
        "branch": branch,
        "event": kind,
        "mode": mode,
        "pr_number": 113 if branch == "research/final-mathematical-closure"
                     else int(hint),
        "case_acceptance": False,
        "claim_acceptance": False,
        "reviewer_selected": False,
        "publication_authorized": False,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head", required=True)
    parser.add_argument("--mode", required=True, choices=sorted(MODES))
    args = parser.parse_args(argv)
    try:
        receipt = authenticate(args.head, args.mode)
        print(json.dumps(receipt, sort_keys=True))
        return 0
    except (SourceDispatchError, KeyError, TypeError, ValueError, OSError) as exc:
        print("OWNER_PRODUCER_SOURCE_BLOCKED:", exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
