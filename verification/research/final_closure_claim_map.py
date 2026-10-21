"""Unreviewed fully-qualified eleven-claim declaration map.

The primary owner is fixed by the existing theorem crosswalk. Supporting
proofs are explicit source obligations, NOT implied by importing one module.
All theorem FQNs and tested scopes are validated lexically, never accepted.
"""
import argparse
import json
from pathlib import Path
import sys

from final_closure_case_receipts import statement_header

ROOT = Path(__file__).resolve().parents[2]
SNAP = ROOT / "research/paper_closures/post_merge_112"
OUTPUT = SNAP / "claim_declaration_map.json"
NS_Q = "PermanssonResearch.Quotient."
NS_M = "PermanssonResearch.MultiAgent."
NS_N = "PermanssonResearch.ReverseSolver.NonlinearPeriodThree."
NS_D = "PermanssonResearch.ReverseSolver."

# Every declaration here is a candidate requiring an actual current-source
# #check/#print axioms, literal statement hash, semantic mutant and human scope review.
SUPPORT = {
    "Q1": [("Quotient/DiscountedCanonicalSourceWitness.lean",
            NS_Q+"DiscountedCanonicalSourceWitness.canonical_discounted_output_error")],
    "Q2": [("Quotient/DiscountedCanonicalMarginClosure.lean",
            NS_Q+"DiscountedCanonicalMarginClosure.actual_canonical_discounted_original_margin")],
    "Q3": [("Quotient/DiscountedCanonicalWitnessExamples.lean",
            NS_Q+"DiscountedCanonicalWitnessExamples.SourceBoundExactWitness.exactKernelPointWitness")],
    "M1": [("MultiAgent/MeasurableProductTwoMatchedProtocols.lean",
            NS_M+"MeasurableProduct.Two.matched_closed_kernel_two"),
           ("MultiAgent/MeasurableProductTwoMatchedProtocols.lean",
            NS_M+"MeasurableProduct.Two.matched_open_kernel_two")],
    "M2": [("MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean",
            NS_M+"MeasurableProduct.Two.matched_closed_loop_original_margin"),
           ("MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean",
            NS_M+"MeasurableProduct.Two.matched_open_loop_original_margin")],
    "M3": [("MultiAgent/MeasurableProductTwoMatchedExamples.lean",
            NS_M+"MeasurableProduct.Two.matched_closed_worlds_both_frozen"),
           ("MultiAgent/MeasurableProductTwoMatchedExamples.lean",
            NS_M+"FinalMatchedAsymmetry.wrong_asymmetric_input_change_is_detectable")],
    "N1": [("ReverseSolver/NonlinearPeriodThreeStationary.lean",
            NS_N+"phase_aware_invariant_weights"),
           ("ReverseSolver/NonlinearPeriodThreeClassGeometry.lean",
            NS_N+"native_phase_aware_actual_true_mass")],
    "N2": [("ReverseSolver/NonlinearPeriodThreeExpectedScore.lean",
            NS_N+"native_phase_aware_actual_score_one"),
           ("ReverseSolver/NonlinearPhaseBlindClassGeometry.lean",
            NS_N+"native_phase_blind_actual_le_five_sixths"),
           ("ReverseSolver/NonlinearPhaseBlindClassGeometry.lean",
            NS_N+"native_phase_blind_actual_attained"),
           ("ReverseSolver/NonlinearPhaseBlindClassGeometry.lean",
            NS_N+"native_actual_phase_aware_strictly_beats_phase_blind")],
    "N3": [("ReverseSolver/NonlinearBooleanClassEvaluator.lean",
            NS_N+"booleanClassFunctional"),
           ("ReverseSolver/NonlinearBooleanClassEvaluator.lean",
            NS_N+"boolean_rational_objective_eq_actual")],
    "D8": [("ReverseSolver/AdaptiveGrammarAdmissionFixture.lean",
            NS_D+"AdaptiveGrammarAdmissionFixture.ConcreteRestrictedBoolean.actual_restricted_menu_admits_both_components"),
           ("ReverseSolver/AdaptiveGrammarAdmissionFixture.lean",
            NS_D+"AdaptiveGrammarAdmissionFixture.ConcreteRestrictedBoolean.actual_restricted_menu_rejects_joint"),
           ("ReverseSolver/AdaptiveGrammarAdmissionFixture.lean",
            NS_D+"AdaptiveGrammarAdmissionFixture.ConcreteRestrictedBoolean.actual_restricted_menu_row_normalized")],
    "D9": [("ReverseSolver/NonlinearMultichainAggregationFixture.lean",
            NS_D+"NonlinearMultichainAggregationFixture.actual_two_absorbing_full_path_mixture"),
           ("ReverseSolver/NonlinearMultichainAggregationFixture.lean",
            NS_D+"NonlinearMultichainAggregationFixture.actual_multichain_classwise_differs_from_barycenter")],
}
TEST_CANDIDATES = {
    "Q1": ["test_final04_source_lean.py"],
    "Q2": ["test_final04_source_lean.py"],
    "Q3": ["test_final04_canonical_output.py"],
    "M1": ["test_final05_measurable_lean.py"],
    "M2": ["test_final05_measurable_lean.py"],
    "M3": ["test_final05_matched_protocols.py"],
    "N1": ["test_final06_native_class_lean.py"],
    "N2": ["test_final06_phaseblind_original.py", "test_final06_actual_score_lean.py"],
    "N3": ["test_final06_c11_evaluator.py"],
    "D8": ["test_final_d08_admission.py"],
    "D9": ["test_final_d09_multichain.py"],
}
EXCLUSIONS = {
    "N2": ["No unrestricted randomized/history-dependent policy optimality",
           "Augmented-state stationary policy is not phase-blind"],
    "D9": ["Current half-versus-five-sixths multichain witness cannot by itself discharge historical five-sixths-versus-one test"],
    "Q2": ["Source PointWitness and full B1 premise must actually be discharged"],
    "M1": ["Conditional-product subclass only; no unrestricted correlated generator"],
}


def generate():
    cross = json.loads((SNAP / "theorem_crosswalk.json").read_text())
    rows = cross["closure_additions"]
    if len(rows) != 11 or set(SUPPORT) != {x["id"] for x in rows}:
        raise ValueError("closure owners changed")
    claims = []
    for row in rows:
        cid = row["id"]
        decls = []
        for partial, fqn in SUPPORT[cid]:
            path = "PermanssonResearch/" + partial
            p = ROOT / path
            if not p.is_file():
                raise ValueError("theorem provider missing: " + path)
            header = statement_header(p.read_text(encoding="utf-8"), fqn)
            decls.append({"path": path, "declaration": fqn,
                          "header_present": bool(header),
                          "review_status": "PENDING_AXIOMS_SEMANTIC_AND_INDEPENDENT_SCOPE"})
        tests = ["verification/research/" + t for t in TEST_CANDIDATES[cid]]
        if any(not (ROOT / test).is_file() for test in tests):
            raise ValueError("claim-level test candidates changed: " + cid)
        claims.append({
            "claim_id": cid, "primary_path": row["path"],
            "original_case_links": row["acceptance_case_ids"],
            "declarations": decls,
            "test_source_candidates": tests,
            "scope_exclusions": EXCLUSIONS.get(cid, []),
            "source_status": "SOURCE_PRESENT_REVIEW_PENDING",
            "accepted": False, "independent_review_receipts": [],
        })
    return {"format": "Permansson.FinalClosureQualifiedClaims.v1",
            "source_baseline_sha": cross["source_baseline_sha"],
            "count": 11, "status": "UNREVIEWED_SOURCE_CANDIDATES",
            "claims": claims}


def render():
    return json.dumps(generate(), sort_keys=True, indent=2,
                      ensure_ascii=False) + "\n"


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--check", action="store_true")
    options = parser.parse_args(argv)
    text = render()
    if options.check:
        if not options.output.is_file() or options.output.read_text() != text:
            print("claim declaration map is stale or missing", file=sys.stderr)
            return 2
    else:
        options.output.parent.mkdir(parents=True, exist_ok=True)
        options.output.write_text(text, encoding="utf-8")
    print(json.dumps({"qualified_claims": 11, "status": "REVIEW_PENDING"}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
