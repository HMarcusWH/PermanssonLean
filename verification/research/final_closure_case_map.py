"""Deterministic original-criterion-to-source work map; NOT an acceptance gate.

No current Git SHA, future reviewer, accepted bit, or fictional test outcome
is embedded in this source-candidate map. Original theorem pins and expected
wording are copied unchanged from the historical 45-case ledger.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
SNAP = ROOT / "research/paper_closures/post_merge_112"
OUTPUT = SNAP / "acceptance_case_source_map.json"

# Every entry is only a candidate test for review, NEVER a passed receipt.
CANDIDATE_TESTS = {
    "X-01": ["test_next03_stochastic_lean.py", "test_paper_x1_matrix_lean.py"],
    "X-04": ["test_next03_tied_start_lean.py"],
    "M-02": ["test_next03_m02_marked_coupling.py"],
    "F-01": ["test_next03_asymmetric_common_swap_lean.py",
             "test_final05_measurable_lean.py"],
    "F-05": ["test_next03_positive_mediation.py"],
    "Q-02": ["test_next04_projection_arithmetic.py"],
    "Q-03": ["test_next03_dependent_three_stage.py", "test_a2_primitive_tv.py"],
    "Q-04": ["test_localized_prefix_compiler.py", "test_next04_original_margin.py"],
    "Q-05": ["test_final04_source_lean.py", "test_next04_original_margin_lean.py"],
    "D-05": ["test_next06_committed_path_law.py"],
    "D-06": ["test_next06_reachable_completion_belief.py"],
    "D-08": ["test_final_d08_admission.py", "test_next06_d08_joint_only_compiler.py"],
    "D-09": ["test_final_d09_multichain.py", "test_final06_phaseblind_original.py"],
    "B-01": ["test_next06_overlap_lean.py"],
    "B-02": ["test_next06_d08_joint_only_compiler.py"],
}


def generate() -> dict:
    ledger = json.loads((SNAP / "acceptance_decisions.json").read_text())
    cross = json.loads((SNAP / "theorem_crosswalk.json").read_text())
    cases = ledger["cases"]
    if len(cases) != 45 or len({x["case_id"] for x in cases}) != 45:
        raise ValueError("original 45-case count/identity changed")
    claims = cross["closure_additions"]
    if len(claims) != 11:
        raise ValueError("expected eleven distinct source closure owners")
    results = []
    for c in cases:
        cid = c["case_id"]
        candidates = ["verification/research/" + n
                      for n in CANDIDATE_TESTS.get(cid, [])]
        for path in candidates:
            if not (ROOT / path).is_file():
                raise ValueError("test candidate no longer exists: " + path)
        results.append({
            "case_id": cid,
            "current_candidate_decision": c["decision"],
            "historical_contract_ids": c["historical_contract_ids"],
            "required_expected_result": c["required_expected_result"],
            "historical_proof_declarations": c["proof_declarations"],
            "new_claim_source_candidates": [
                {"id": row["id"], "path": row["path"]}
                for row in claims if cid in row["acceptance_case_ids"]],
            "test_source_candidates": candidates,
            "case_specific_test_status": (
                "CANDIDATES_REQUIRE_CRITERION_RELEVANCE_REVIEW" if candidates
                else "MISSING_CASE_SPECIFIC_TEST_SELECTION"),
            "remaining_obligations": c["remaining_obligations"],
            "evidence": {"compiler": [], "positive": [], "negative": [],
                         "check_runs": [], "review": []},
            "effective_accepted": False,
        })
    return {
        "format": "Permansson.OriginalAcceptanceCaseSourceMap.v1",
        "source_baseline_sha": ledger["source_baseline_sha"],
        "status": "UNREVIEWED_CANDIDATE_ONLY",
        "original_cases": 45,
        "original_atlas_contracts": cross["historical_contract_count"],
        "new_closure_owners": 11,
        "cases": results,
        "qualification": ("Test candidates are a review work queue. Missing "
                          "case-specific tests remain explicitly unassigned; "
                          "no global CI check or source name establishes case acceptance."),
    }


def render() -> str:
    return json.dumps(generate(), indent=2, sort_keys=True,
                      ensure_ascii=False) + "\n"


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, default=OUTPUT)
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args(argv)
    value = render()
    if args.check:
        if not args.output.is_file() or args.output.read_text() != value:
            print("case source map differs from exact original ledger", file=sys.stderr)
            return 2
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(value, encoding="utf-8")
    print(json.dumps({"cases": 45,
                      "test_assigned": sum(bool(c["test_source_candidates"])
                                           for c in generate()["cases"]),
                      "status": "UNREVIEWED_CANDIDATE_ONLY"}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
