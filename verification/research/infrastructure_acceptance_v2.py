"""PR113 proposed V2 T/T2+A2 required evidence gate (NOT INSTALLED).

Versioned input source, exactly 25 historical / 30 current workflow sources.
Authentic GitHub run/job/attempt/check/artifact and current-H independent
security reviewer decisions are REQUIRED. Never interpret an infrastructure
receipt as mathematical certification or owner merge/publication authorization.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

import infrastructure_acceptance as legacy
from final_closure_authenticate import (
    REQUIRED, authenticated_checks, git as real_git, live as real_live,
    paginate as real_paginate,
)
import release_target
from pr113_historical_evidence_contract_v2 import (
    validate_envelope, parse_envelope,
)
from pr113_workflow_profile_v2 import audit as workflow_audit
from pr113_historical_intake_v2 import (
    inspect_T_v2, inspect_A2_v2,
)

ROOT = Path(__file__).resolve().parents[2]
FORMAT = "Permansson.PR113.InfrastructureEvidence.v2"
ACTIVE_WORKFLOW = legacy.ACTIVE_WORKFLOW
AUTHORITY_PATH = legacy.AUTHORITY_PATH
EXPECTED_ARTIFACTS = legacy.EXPECTED_ARTIFACTS
EVIDENCE_FIELDS = legacy.EVIDENCE_FIELDS
authenticate_original_zip = legacy.authenticate_original_zip
inspect_zip = legacy.inspect_zip
from pr113_a2_dependency_bridge_v2 import verify_A2_dependency_bridge
exact_committed_lake_blob = legacy.exact_committed_lake_blob
exact_committed_blob = legacy.exact_committed_blob
from pr113_secure_security_review_v3 import (
    authority_policy, approved_security_review,
)
sha = legacy.sha
need = legacy.need
InfrastructureError = legacy.InfrastructureError


def checked_profile(head, *, git=real_git):
    """Source identity from real PR merge S or approved main merge M.

    Runtime checkout must have the exact H tree. The current 30 source
    profile is measured from Git objects; its digest is not a human review.
    """
    checked = git("rev-parse", "HEAD")
    need(isinstance(checked, str) and len(checked) == 40 and
         git("cat-file","-t",checked) == "commit" and
         git("cat-file","-t",head) == "commit",
         "v2 checkout/H source must be genuine Git commits")
    if checked != head:
        need(git("show","-s","--format=%P",checked).split() ==
                 [release_target.B113,head],
             "v2 checkout S/M must have exact ordered original B113 and reviewed H")
    need(git("rev-parse", checked + "^{tree}") ==
             git("rev-parse", head + "^{tree}"),
         "v2 source is not the same exact Git tree as reviewed H")
    result = workflow_audit(ROOT, checked, phase="active")
    need(result.get("head_sha") == checked
         and result.get("current_reviewed_workflow_count") == 30
         and result.get("historical_original_workflow_count") == 25
         and result.get("independent_security_review") is False,
         "current T2 profile cannot be inferred from 25-file evidence")
    return result


def inspect_T(files, head):
    profile = checked_profile(head)
    return inspect_T_v2(
        files, head, profile_sha256=profile["current_source_profile_sha256"])


def inspect_A2(files, head):
    checked_profile(head)
    return inspect_A2_v2(files, head)


def check_historical_only(payload, T_bytes, A2_bytes, *,
                          git=real_git, live=real_live,
                          paginate=real_paginate):
    """Noncircular mandatory check: real dual producers and review, NOT 12/12."""
    validate_envelope(payload)
    need(isinstance(payload, dict) and set(payload) == EVIDENCE_FIELDS
         and payload.get("format") == FORMAT,
         "unversioned/forged historical input envelope")
    source = payload.get("target")
    release_target.candidate_bindings(source)
    target = release_target.bind(
        source, intent=release_target.exact_intent(
            source["head_sha"], git=git), git=git, live=live)
    need(target["phase"] == "infrastructure_premerge",
         "new certification target cannot reuse PR113 historical authority")
    head = target["head_sha"]
    profile = checked_profile(head, git=git)
    workflow_raw = exact_committed_blob(head, ACTIVE_WORKFLOW, git=git)
    workflow = workflow_raw.decode("utf-8")
    need(workflow.startswith("# Review-pending source-controlled")
         and "historical-T-and-H-unreviewed" in workflow
         and "historical-A2-and-H-unreviewed" in workflow,
         "genuine reviewed producing workflow missing from exact H")
    authentic_T = authenticate_original_zip(
        "T", payload["historical_T"], T_bytes, head, live=live)
    authentic_A2 = authenticate_original_zip(
        "A2", payload["historical_A2"], A2_bytes, head, live=live)
    t = inspect_T_v2(
        inspect_zip(T_bytes), head,
        profile_sha256=profile["current_source_profile_sha256"])
    a_files = inspect_zip(A2_bytes)
    a = inspect_A2_v2(a_files, head)
    a["dependency_bridge_sha256"] = verify_A2_dependency_bridge(
        a_files, head,
        manifest_raw=exact_committed_lake_blob(head, git=git))
    policy = authority_policy(head, git=git)
    pr = live("/pulls/113")
    attestation = {
        "head_sha": head,
        "workflow_sha256": sha(workflow_raw),
        "T_artifact_sha256": sha(T_bytes),
        "A2_artifact_sha256": sha(A2_bytes),
        "original_base_sha": release_target.B113,
    }
    approved_security_review(
        payload["security_review_id"],
        (pr.get("user") or {}).get("login"),
        head, attestation, policy, paginate=paginate)
    return {
        "format": "Permansson.PR113.HistoricalDualRequiredSourceReceipt.v2",
        "status": "HISTORICAL_T_AND_A2_GENUINE_WITH_INDEPENDENT_SECURITY_REVIEW",
        "source_head": head,
        "base_sha": release_target.B113,
        "synthetic_sha": target["synthetic_sha"],
        "workflow_sha256": sha(workflow_raw),
        "workflow_profile_sha256": profile["current_source_profile_sha256"],
        "historical_original_workflow_count": 25,
        "current_reviewed_workflow_count": 30,
        "T_execution": t,
        "A2_execution": a,
        "genuine_artifacts": {"T": authentic_T, "A2": authentic_A2},
        "security_review_id": payload["security_review_id"],
        "historical_source_and_security_review_authenticated": True,
        "required_ci_successful": 0,
        "independent_mathematical_review": False,
        "accepted_original_cases": 0,
        "accepted_new_claims": 0,
        "merged_main_sha": None,
        "merge_authorized": False,
        "publication_authorized": False,
        "full_release_approved": False,
    }


def check_evidence(payload, T_bytes, A2_bytes, *,
                   git=real_git, live=real_live,
                   paginate=real_paginate, checks=authenticated_checks):
    """Later aggregate 12 genuine checks. It cannot self-certify its caller."""
    validate_envelope(payload, require_all_checks=True)
    old = check_historical_only(
        payload,T_bytes,A2_bytes,git=git,live=live,paginate=paginate)
    head = old["source_head"]
    observed = checks(head)
    requested = payload.get("source_bound_ci")
    need(isinstance(requested, list) and len(requested) == len(REQUIRED)
         and {x.get("name") for x in requested if isinstance(x,dict)} ==
             REQUIRED,
         "12 required source contexts not listed")
    for item in requested:
        need(isinstance(item,dict) and set(item) == {"name","id","head_sha"}
             and item.get("head_sha") == head
             and type(item.get("id")) is int
             and item["name"] in observed
             and item["id"] == observed[item["name"]]["id"],
             "required 12-context check missing, wrong source or stale run")
    result=dict(old)
    result.update({
        "format": "Permansson.PR113.InfrastructureAcceptanceReceipt.v2",
        "status": "INFRASTRUCTURE_READY_FOR_SEPARATE_OWNER_MERGE_DECISION",
        "required_ci_successful": len(REQUIRED),
        "independent_security_review_authenticated": True,
        "mathematical_acceptance": False,
        "owner_merge_authorized": False,
        "publication_authorized": False,
    })
    return result


def main(argv=None):
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--evidence",required=True,type=Path)
    ap.add_argument("--historical-T-zip",required=True,type=Path)
    ap.add_argument("--historical-A2-zip",required=True,type=Path)
    ap.add_argument("--out",required=True,type=Path)
    ap.add_argument("--historical-only",action="store_true")
    args=ap.parse_args(argv)
    try:
        from pr113_boundary_io import detached_destination
        dest=detached_destination(args.out, ROOT)
        envelope=args.evidence.read_bytes()
        need(0 < len(envelope) <= 64*1024,
             "missing/unbounded authentic versioned evidence envelope")
        check=check_historical_only if args.historical_only else check_evidence
        receipt=check(parse_envelope(
            envelope, require_all_checks=not args.historical_only),
            args.historical_T_zip.read_bytes(),
                      args.historical_A2_zip.read_bytes())
        dest.parent.mkdir(parents=True,exist_ok=True)
        with dest.open("x",encoding="utf-8") as f:
            json.dump(receipt,f,indent=2,sort_keys=True)
            f.write("\n")
        print(json.dumps({"status":receipt["status"],
                          "source_head":receipt["source_head"]},sort_keys=True))
        return 0
    except (OSError, ValueError, TypeError, KeyError, RuntimeError) as exc:
        print("PR113 V2 INFRASTRUCTURE NOT ACCEPTED:",exc,file=sys.stderr)
        return 2


if __name__=="__main__":
    raise SystemExit(main())
