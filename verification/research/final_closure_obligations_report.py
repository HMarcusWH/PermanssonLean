"""Readable 45-case/11-claim acceptance backlog from frozen candidate maps.

The report is not an acceptance decision. Never rewrite original criteria,
promote reviewer statuses, or infer proof completeness from imported modules.
"""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
SNAP = ROOT/"research/paper_closures/post_merge_112"
OUTPUT = SNAP/"acceptance_obligations_report.md"


def safe(value):
    return str(value).replace("|", "\\|").replace("\n", " ")


def render():
    cases = json.loads((SNAP/"acceptance_case_source_map.json").read_text())
    claims = json.loads((SNAP/"claim_declaration_map.json").read_text())
    if cases["original_cases"] != 45 or claims["count"] != 11:
        raise ValueError("candidate case or claim map incomplete")
    source_cases = cases["cases"]
    pending = [c for c in source_cases
               if c["current_candidate_decision"] == "PENDING"]
    partial = [c for c in source_cases
               if c["current_candidate_decision"] == "PARTIAL_SCOPE"]
    if len(pending) != 15 or len(partial) != 30:
        raise ValueError("unexpected candidate case statuses")
    lines = [
        "# Permansson PR #113 — original acceptance obligation work queue",
        "",
        "**CANDIDATE / NOT ACCEPTED / NO INDEPENDENT REVIEW.**",
        "",
        "This report is derived from unchanged original criteria and source mappings."
        " It is not an exact-head CI receipt or independent scholarly approval.",
        "",
        f"- Original cases: {len(source_cases)}; pending: {len(pending)};"
        f" partial scope: {len(partial)}; independently accepted: 0.",
        f"- New claim owners: {len(claims['claims'])}; accepted: 0.",
        "- Candidate test paths below are NOT verified as sufficient"
        " for their original criteria.",
        "",
        "## Original acceptance requirements (all 45)",
        "",
        "| Case | Candidate state | Original required result |"
        " Historical theorem pins | Candidate tests |",
        "|---|---|---|---:|---|",
    ]
    for row in source_cases:
        lines.append(
            "| " + safe(row["case_id"]) +
            " | " + safe(row["current_candidate_decision"]) +
            " | " + safe(row["required_expected_result"]) +
            " | " + str(len(row["historical_proof_declarations"])) +
            " | " + safe(", ".join(row["test_source_candidates"]) or
                           "TEST SELECTION STILL UNASSIGNED") + " |")
    lines.extend([
        "",
        "## Fifteen case-specific historical objections",
        "",
        "| Case | Still-to-be-reconciled obligation(s) |",
        "|---|---|",
    ])
    for row in pending:
        residuals = [
            x for x in row["remaining_obligations"]
            if not x.startswith("Exact-head compiler and transitive-axiom receipts")
            and not x.startswith("Strengthened original acceptance fixture")]
        lines.append("| " + row["case_id"] + " | " +
                     safe(" / ".join(residuals) or "NO REVIEWED DISPOSITION") + " |")
    lines.extend([
        "",
        "## Eleven candidate claim owners (not yet accepted)",
        "",
        "| Claim | Owner source | Fully qualified declaration count | Status |",
        "|---|---|---:|---|",
    ])
    for row in claims["claims"]:
        lines.append("| " + row["claim_id"] + " | " + row["primary_path"] +
                     " | " + str(len(row["declarations"])) +
                     " | SOURCE_PRESENT_REVIEW_PENDING |")
    lines.extend([
        "",
        "## Closure protocol",
        "",
        "Each original case requires a correct Lean source/premise binding,"
        " a positive control and semantically false mutant, genuine check-run"
        " IDs and a separately authenticated non-author exact-H case-specific"
        " review. Source-only PENDING/PARTIAL decisions cannot self-promote.",
        "",
        "After source H freezes, signed reviewer and effective acceptance overlays"
        " remain DETACHED. Any approved mathematical paper additionally requires"
        " genuine merged M, page-by-page PDF inspection and independent"
        " postmerge scholarly signoff. A compiler-green source does not certify"
        " empirical GR/PR or unrestricted randomized policy optimality.",
        "",
    ])
    return "\n".join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--check", action="store_true")
    a = parser.parse_args(argv)
    result = render()
    if a.check:
        if not a.output.is_file() or a.output.read_text() != result:
            print("candidate obligations report stale", file=sys.stderr)
            return 2
    else:
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(result, encoding="utf-8")
    print(json.dumps({"status": "UNREVIEWED_CASE_WORK_QUEUE",
                      "original_cases": 45, "new_claims": 11}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
