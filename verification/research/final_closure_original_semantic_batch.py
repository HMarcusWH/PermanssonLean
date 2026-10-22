"""Execute nine frozen original-case semantic mutants as DETACHED candidates.

This file bridges disposable unittest mutants to the complete byte-preserving
mutation verifier. Every mutant is the genuine on-repository Lean provider
plus exactly one explicit mathematically false assertion. Original imports
and declarations are not replaced. The positive control compiles the
unmodified provider; the false source must be rejected semantically.

No artifact emitted here is independently reviewed or CI-attributed.
Only a real external artifact collected from a known GitHub producing job
can be considered for the separate authenticated receipt contract.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import tempfile
import textwrap

from final_closure_mutation_evidence import (
    MutationEvidenceError, produce, seal_logs, git_head
)
from final_closure_case_receipts import ROOT

MAP = ROOT / "research/paper_closures/post_merge_112/acceptance_case_source_map.json"

# Each source statement is about the ACTUAL typed original provider, not a
# free-standing surrogate number or an unrelated source.
SPECS = {
    "F-03": {
        "source": "PermanssonResearch/MultiAgent/F03ActualInfeasibleAnchor.lean",
        "test_path": "verification/research/test_f03_actual_infeasible_strict_anchor_lean.py",
        "method": "test_false_feasible_anchor_with_conflicting_own_fibre_rejected",
        "body": """
open PermanssonResearch.MultiAgent
open PermanssonResearch.MultiAgent.F03ActualInfeasibleAnchor
example : ∃ a : PlayerTwoMechanism Unit Bool Unit Unit Unit Bool,
  IsStrictlyNonReactive a ∧
    ∀ y : Y, a.action y (legal y) = 1 := by
  exact no_feasible_original_strict_anchor
""",
    },
    "D-02": {
        "source": "PermanssonResearch/ReverseSolver/CompactResidenceMonitor.lean",
        "test_path": "verification/research/test_final_original_chronological_false_lean.py",
        "method": "test_D_02_false_retryable_residence_word",
        "body": """
open PermanssonResearch.ReverseSolver.FiniteMonitor
example :
  (residenceScan (fun z : Bool => z = true) 1
    [true, false, true, true]).2 = false := by
  have hcorrect :
    (residenceScan (fun z : Bool => z = true) 1
      [true, false, true, true]).2 = true := by decide
  exact hcorrect
""",
    },
    "D-03": {
        "source": "PermanssonResearch/ReverseSolver/AvoidResidenceMonitor.lean",
        "test_path": "verification/research/test_final_original_chronological_false_lean.py",
        "method": "test_D_03_false_danger_after_success_revokes_it",
        "body": """
open PermanssonResearch.ReverseSolver.FiniteMonitor
example :
  (avoidRun (fun b : Bool => b = true)
    (fun b : Bool => b = false) 0 ((0,false),false)
    [true, false]).1.2 = false := by
  exact danger_after_success_does_not_undo
""",
    },
    "D-04": {
        "source": "PermanssonResearch/ReverseSolver/SolverBoundaryWitnesses.lean",
        "test_path": "verification/research/test_final_original_risk_belief_false_lean.py",
        "method": "test_D_04_false_hard_risk_budget_accepts_p_one",
        "body": """
open PermanssonResearch.ReverseSolver.SolverBoundaryWitnesses
example : ((1 : ℚ) / 10 ≤ 1/20) := by
  exact hard_risk_half_mixture_attains.2.2
""",
    },
    "D-05": {
        "source": "PermanssonResearch/ReverseSolver/CommittedVsRectangularPathFixture.lean",
        "test_path": "verification/research/test_final_original_chronological_false_lean.py",
        "method": "test_D_05_false_committed_rectangular_path_law_equality",
        "body": """
open PermanssonResearch.ReverseSolver.CommittedVsRectangular
example :
  (pathLaw false true).expectation survivesBoth =
    min ((pathLaw false false).expectation survivesBoth)
        ((pathLaw true true).expectation survivesBoth) := by
  rw [rectangular_actual_success,
      committed_false_actual_success, committed_true_actual_success]
  have hneq : (1/100 : ℝ) ≠ 9/100 := by norm_num
  exact hneq
""",
    },
    "D-06": {
        "source": "PermanssonResearch/ReverseSolver/ReachableCompletionBeliefFixture.lean",
        "test_path": "verification/research/test_final_original_risk_belief_false_lean.py",
        "method": "test_D_06_false_same_readout_identifies_completion",
        "body": """
open PermanssonResearch.ReverseSolver.ReachableCompletionBelief
example : (model.filter 0 initial [(false, ())]).weight true =
  (model.filter 0 initial [(true, ())]).weight true := by
  have hneq :
      (model.filter 0 initial [(false, ())]).weight true ≠
      (model.filter 0 initial [(true, ())]).weight true := by
    rw [reachable_posteriors_disagree.1,
        reachable_posteriors_disagree.2]
    norm_num
  exact hneq
""",
    },
    "Q-03": {
        "source": "PermanssonResearch/Probability/DependentThreeStageSaturation.lean",
        "test_path": "verification/research/test_final_actual_product_reporting_false_lean.py",
        "method": "test_Q_03_false_independent_error_mass",
        "body": """
open PermanssonResearch.Probability.DependentThreeStage
example : dependentLaw.atom (true, (true,true)) = (9/20 : ℝ) := by
  exact true_history_mass
""",
    },
    "E-05": {
        "source": "PermanssonResearch/Specialized/E05FullGramMaskingCountermodel.lean",
        "test_path": "verification/research/test_e05_full_gram_masking_lean.py",
        "method": "test_false_unqualified_full_gram_negativity_rejected",
        "body": """
open PermanssonResearch.Specialized.E05FullGramMaskingCountermodel
open PermanssonResearch.Specialized
open scoped InnerProductSpace
example {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {c : ℝ} (hc : 0 < c)
    (x y : E) (hgap : 0 < gramGap x y) :
    c * (⟪x, gramWitness x y⟫_ℝ ^ 2 -
         ⟪y, gramWitness x y⟫_ℝ ^ 2) +
    2 * c * gramGap x y ^ 2 < 0 := by
  exact (original_signed_negative_but_total_positive hc x y hgap).2
""",
    },
    "Q-04": {
        "source": "PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixExamples.lean",
        "test_path": "verification/research/test_final_actual_product_reporting_false_lean.py",
        "method": "test_Q_04_false_zero_intervention_report_error",
        "body": """
open PermanssonResearch.ConstitutiveQuasi.LocalizedExamples
example : dist (0 : ℝ) (1/10) ≤ 0 := by
  exact cannot_omit_treatment_report_error
""",
    },
    "A-03": {
        "source": "PermanssonResearch/Probability/KantorovichTV.lean",
        "test_path": "verification/research/test_pr113_semantic_boundary_candidates.py",
        "method": "test_A_03_unbounded_TV_does_not_bound_W1",
        "body": """
namespace PermanssonResearch.Probability
open PermanssonLean.ProbabilitySupport
example {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (C : ℝ) :
    ¬ ∃ n : ℕ, (haveI := tailMix_isProbability hε.le hε1 n
      eventTotalVariation (Measure.dirac (0 : ℝ)) (tailMix ε n) ≤ ε) ∧
      ¬ W1DualLE (Measure.dirac (0 : ℝ)) (tailMix ε n) (C * ε) := by
  exact tv_does_not_control_w1_on_real hε hε1 C
end PermanssonResearch.Probability
""",
    },
    "C-01": {
        "source": "PermanssonResearch/MultipleLimit/GrowingBlockCounterexample.lean",
        "test_path": "verification/research/test_pr113_semantic_boundary_candidates.py",
        "method": "test_C_01_bounded_descriptor_occupation_nonconvergence",
        "body": """
namespace PermanssonResearch.MultipleLimit.GrowingBlock
open PermanssonResearch.MultipleLimit.FiniteStateOccupation
open Filter MeasureTheory
open scoped Topology
example :
    ∃ π : ProbabilityMeasure (Fin 2),
      Tendsto (fun n => empiricalOccupation descriptor (n+1) (Nat.succ_pos n))
        atTop (𝓝 π) := by
  exact descriptor_occupations_do_not_converge
end PermanssonResearch.MultipleLimit.GrowingBlock
""",
    },
    "D-07": {
        "source": "PermanssonResearch/ReverseSolver/InfiniteSafetyLeakage.lean",
        "test_path": "verification/research/test_pr113_semantic_boundary_candidates.py",
        "method": "test_D_07_finite_survival_does_not_imply_infinite_safety",
        "body": """
namespace PermanssonResearch.ReverseSolver.InfiniteSafety
example : limitValue leakageSystem leakageTarget 0 = (99 : ℝ) / 100 := by
  exact leakage_limitValue
end PermanssonResearch.ReverseSolver.InfiniteSafety
""",
    },
    "E-01": {
        "source": "PermanssonResearch/Specialized/SeamReduction.lean",
        "test_path": "verification/research/test_pr113_semantic_boundary_candidates.py",
        "method": "test_E_01_seam_invisibility_does_not_force_rank_one",
        "body": """
namespace PermanssonResearch.Specialized
example (H : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 2)
    (hsym : ∀ i j, H i j = H j i)
    (hseam : ∀ i j, seam H p i j = 0) :
    H.rank ≤ 1 := by
  exact seam_rank_le_two H p hsym hseam
end PermanssonResearch.Specialized
""",
    },
}


def frozen_spec(case_id: str, *, root: Path = ROOT) -> tuple[dict, bytes]:
    if case_id not in SPECS:
        raise MutationEvidenceError("unregistered original semantic mutation case")
    entry = SPECS[case_id]
    if not isinstance(entry, dict) or set(entry) != {
        "source", "test_path", "method", "body",
    }:
        raise MutationEvidenceError("semantic case contract is malformed")
    rows = json.loads((root / "research/paper_closures/post_merge_112/"
                       "acceptance_case_source_map.json").read_bytes())
    matches = [row for row in rows.get("cases", [])
               if row.get("case_id") == case_id]
    if len(matches) != 1 or rows.get("original_cases") != 45:
        raise MutationEvidenceError("case ID not in exact original acceptance map")
    original = matches[0]
    if original.get("effective_accepted") is not False:
        raise MutationEvidenceError("unreviewed mutation cannot inherit approval")
    requested = ("verification/research/" +
                 Path(entry["test_path"]).name, entry["method"],
                 "SEMANTIC_NEGATIVE")
    selected = {(row.get("path"), row.get("method"), row.get("role"))
                for row in original.get("test_method_candidates", [])
                if isinstance(row, dict)}
    if requested not in selected:
        raise MutationEvidenceError("semantic mutant is not a selected original method")
    relative = Path(entry["source"])
    if (relative.is_absolute() or ".." in relative.parts or
        not relative.as_posix().startswith("PermanssonResearch/") or
        relative.suffix != ".lean"):
        raise MutationEvidenceError("unsafe/non-original Lean provider path")
    candidate_source = root / relative
    original_path = candidate_source.resolve()
    if (candidate_source.is_symlink() or
        not original_path.is_relative_to(root.resolve()) or
        not original_path.is_file() or original_path.is_symlink()):
        raise MutationEvidenceError("actual original Lean source unavailable")
    candidate_test = root / entry["test_path"]
    test_path = candidate_test.resolve()
    if (candidate_test.is_symlink() or
        not test_path.is_relative_to(root.resolve()) or
        not test_path.is_file() or test_path.is_symlink()):
        raise MutationEvidenceError("original named test unavailable")
    body = textwrap.dedent(entry["body"]).strip() + "\n"
    if any(re.match(r"(?i)^\s*(?:import|axiom|sorry|admit)\b", line)
           for line in body.splitlines()):
        raise MutationEvidenceError("false fixture may not alter imports or introduce axioms")
    if len(body.encode("utf-8")) > 4096:
        raise MutationEvidenceError("unbounded original semantic mutation body")
    original_bytes = original_path.read_bytes()
    if not original_bytes or len(original_bytes) > 4*1024*1024:
        raise MutationEvidenceError("unbounded original source")
    mutated = (original_bytes +
               ("\n/- ORIGINAL CASE " + case_id +
                ": FALSE SEMANTIC TEST ONLY -/\n" + body).encode("utf-8"))
    expected_imports = [line for line in original_bytes.decode("utf-8").splitlines()
                        if line.startswith("import ")]
    changed_imports = [line for line in mutated.decode("utf-8").splitlines()
                       if line.startswith("import ")]
    if expected_imports != changed_imports:
        raise MutationEvidenceError("source import identity changed")
    return entry, mutated


def run_one(head: str, case_id: str, out: Path) -> dict:
    if (not re.fullmatch(r"[a-f0-9]{40}", head) or head != git_head()):
        raise MutationEvidenceError("source checkout is not exact frozen H")
    out = out.resolve()
    if (out.exists() or out.is_relative_to(ROOT.resolve()) or
        ROOT.resolve().is_relative_to(out)):
        raise MutationEvidenceError("must write to a new detached output root")
    entry, mutated = frozen_spec(case_id)
    out.mkdir(parents=True, exist_ok=False)
    with tempfile.TemporaryDirectory(prefix="mutant-", dir=out) as td:
        input_path = Path(td) / "OriginalFalse.lean"
        input_path.write_bytes(mutated)
        directory = out / "source_logs"
        result = produce(
            head, true_source=ROOT / entry["source"],
            mutant=input_path,
            test_path=ROOT / entry["test_path"],
            test_name=entry["method"],
            case_id=case_id, claim_ids=[], out=directory)
    archive = out / "semantic_candidate_logs.zip"
    archive_digest = seal_logs(out / "source_logs", archive)
    return {
        "format": "Permansson.OriginalSemanticMutantCandidate.v1",
        "status": "DETACHED_UNREVIEWED_UNATTRIBUTED",
        "source_head": head,
        "case_id": case_id,
        "test_path": entry["test_path"],
        "test_name": entry["method"],
        "source_path": entry["source"],
        "mutant_sha256": hashlib.sha256(mutated).hexdigest(),
        "detached_bundle_sha256": archive_digest,
        "mutation_record": result,
        "ci_check_run_id": None,
        "independent_review": False,
        "full_mathematical_acceptance": False,
    }


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--head", required=True)
    parser.add_argument("--case-id", choices=sorted(SPECS), required=True)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        result = run_one(args.head, args.case_id, args.out)
        (args.out / "unreviewed_candidate.json").write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n",
            encoding="utf-8")
    except (MutationEvidenceError, OSError, ValueError, KeyError) as exc:
        print("ORIGINAL SEMANTIC EVIDENCE BLOCKED:", exc, file=sys.stderr)
        return 2
    print(json.dumps({k: result[k] for k in (
        "status", "source_head", "case_id", "detached_bundle_sha256",
    )}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
