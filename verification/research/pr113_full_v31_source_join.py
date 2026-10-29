"""Full PR113 v3+v3.1 exact-H source execution join (NOT mathematical approval).

The only input to this join is the result of two independent *live*
authentication passes: the mandatory original 21 producer ZIPs/259 proof
types/45+11 semantic owner routes and all 76 additional original GitHub
producer owners with actual positive/negative source and compiler log bytes.
Neither an unverified catalog JSON nor 12 green checks alone satisfies it.

Real security/mathematical review, actual merged main M and publication are
separate downstream gates. This program never creates approvals or a merge.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from pr113_final_source_readiness import (
    inspect as original_inspect, ReadinessError, ROOT,
)
from final_closure_extra_producers_v31 import (
    assemble_review_pending, ControlProducerError,
)


class CombinedEvidenceError(ValueError):
    pass


def require(ok, reason):
    if not ok:
        raise CombinedEvidenceError(reason)


def join_authenticated_evidence(original, additional):
    """Join verified *execution* records, not author-asserted acceptance flags."""
    require(isinstance(original, dict) and
            original.get("status") ==
                "COMPLETE_SOURCE_EVIDENCE_UNREVIEWED_NOT_ACCEPTED" and
            original.get("candidate_controls_complete") is True and
            original.get("source_proofs") == 259 and
            original.get("producer_shards") == 21 and
            original.get("exact_head_required_ci") == 12 and
            original.get("actual_github_producer_shards") == 21 and
            original.get("cases_with_positive_negative_controls") == 45 and
            original.get("claims_with_positive_negative_controls") == 11 and
            original.get("independent_case_reviews") == 0 and
            original.get("independent_claim_reviews") == 0,
            "original v3 mandatory real source evidence is incomplete")
    head = original["source_head"]
    require(isinstance(additional, dict) and
            additional.get("format") ==
                "Permansson.PR113.ControlCIAuthenticationCandidate.v3.1" and
            additional.get("status") ==
                "ALL_ADDITIONAL_CONTROLS_SOURCE_ATTRIBUTED_UNREVIEWED" and
            additional.get("head_sha") == head and
            additional.get("original_21_producing_artifacts_still_required") == 21 and
            additional.get("original_case_positives") == 45 and
            additional.get("legacy_case_negatives") == 20 and
            additional.get("claim_positive_negative_pairs") == 11 and
            additional.get("accepted_cases") == 0 and
            additional.get("accepted_claims") == 0 and
            additional.get("schema_security_approved") is False and
            additional.get("independent_mathematical_review") is False and
            additional.get("full_release_approved") is False,
            "new controls are not authenticated unreviewed exact-H source jobs")
    rows = additional.get("source_owned_controls")
    checks = additional.get("actual_execution_member_validation")
    require(isinstance(rows, list) and len(rows) == 76 and
            all(isinstance(x, dict) for x in rows) and
            len({(x.get("kind"), x.get("owner_id")) for x in rows}) == 76 and
            isinstance(checks, dict) and
            checks.get("format") ==
                "Permansson.PR113.GenuineSourceExecutionBytes.v1" and
            checks.get("status") ==
                "ACTUAL_CONTROL_BYTES_REVALIDATED_UNREVIEWED" and
            checks.get("source_head") == head and
            checks.get("source_owner_count") == 76 and
            checks.get("canonical_routes_bound") is True and
            checks.get("legacy_original_captures_bound") is True and
            checks.get("claim_positive_negative_directions") == 22 and
            checks.get("execution_log_members_checked", 0) >= 76 and
            checks.get("independent_review") is False and
            checks.get("mathematical_acceptance") is False and
            checks.get("publication_approved") is False,
            "true and false source-control execution members not revalidated")
    from collections import Counter
    kinds = Counter(row["kind"] for row in rows)
    require(kinds == {"original_positive": 45, "legacy_negative": 20,
                      "claim_pair": 11} and
            {r["owner_id"] for r in rows if r["kind"] == "claim_pair"} ==
            {"Q1", "Q2", "Q3", "M1", "M2", "M3", "N1", "N2", "N3",
             "D8", "D9"},
            "source owner classes cannot be substituted")
    return {
        "format": "Permansson.PR113.FullExecutionEvidenceJoin.v3.1",
        "status": "ALL_SOURCE_EXECUTION_AUTHENTICATED_UNREVIEWED",
        "head_sha": head,
        "synthetic_sha": original["synthetic_sha"],
        "original_ci_checks": 12,
        "original_genuine_producer_zips": 21,
        "kernel_theorem_receipts": 259,
        "case_positive_negative_controls": 45,
        "claim_positive_negative_pairs": 11,
        "additional_gh_source_owner_records": 76,
        "additional_log_members_verified":
            checks["execution_log_members_checked"],
        "independent_review": False,
        "security_approval": False,
        "merge_authorized": False,
        "mathematical_release_approved": False,
        "publication_authorized": False,
    }


def execute(head, synthetic, original_json, original_zip, extra_contract,
            extra_dir, workflow_blobs, additional_report, joined_report):
    out = Path(joined_report).absolute()
    v31 = Path(additional_report).absolute()
    for p in (out, v31):
        require(not p.exists() and not p.is_symlink() and
                not any(x.is_symlink() for x in p.parents) and
                not p.is_relative_to(ROOT.resolve()),
                "joined source provenance must be fresh and outside Git source")
    require(out != v31, "source run and join outputs cannot overwrite each other")
    original = original_inspect(head, synthetic, original_json, original_zip)
    additional = assemble_review_pending(
        head, original_json, original_zip, extra_contract, extra_dir,
        workflow_blobs, v31)
    result = join_authenticated_evidence(original, additional)
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(result, sort_keys=True, indent=2) + "\n")
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head", required=True)
    parser.add_argument("--synthetic", required=True)
    parser.add_argument("--original-receipts", type=Path, required=True)
    parser.add_argument("--original-zip", type=Path, required=True)
    parser.add_argument("--additional-contract", type=Path, required=True)
    parser.add_argument("--additional-zips", type=Path, required=True)
    parser.add_argument("--workflow-blob-candidates", type=Path, required=True)
    parser.add_argument("--additional-report", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        result = execute(
            args.head, args.synthetic, args.original_receipts,
            args.original_zip, args.additional_contract,
            args.additional_zips, args.workflow_blob_candidates,
            args.additional_report, args.out)
        print(json.dumps({"status": result["status"],
                          "head": result["head_sha"],
                          "owner_count": 76}, sort_keys=True))
        return 0
    except (CombinedEvidenceError, ReadinessError,
            ControlProducerError, OSError, ValueError,
            TypeError, KeyError) as exc:
        print("PR113 COMPLETE SOURCE EXECUTION JOIN BLOCKED:", exc,
              file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
