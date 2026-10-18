import PermanssonResearch.ReverseSolver.PolytopeLinearProgram

namespace PermanssonResearch.ReverseSolver.ExactPolytope.Regression

open Matrix

set_option maxRecDepth 32768
set_option maxHeartbeats 0

def riskMatrix : Matrix (Fin 3) (Fin 1) ℚ := ![![-1], ![1], ![1/10]]
def riskBounds : Fin 3 → ℚ := ![0, 1, 1/20]

/-- Exact exhaustive enumeration returns the required randomized choice. -/
theorem risk_optimizer_half :
    optimizeRational riskMatrix riskBounds ![1/10] = some ![1/2] := by
  unfold optimizeRational rationalCandidateList activeSelections
  rw [Fin.sort_univ]
  decide +kernel

theorem risk_success_at_half : (4/5 : ℚ) + (1/2)/10 = 17/20 := by norm_num

theorem risk_deterministic_full_infeasible :
    ¬ rationalFeasible riskMatrix riskBounds ![1] := by decide +kernel

theorem risk_negative_budget_infeasible :
    optimizeRational riskMatrix ![0,1,-1/20] ![1/10] = none := by
  unfold optimizeRational rationalCandidateList activeSelections
  rw [Fin.sort_univ]
  decide +kernel

/-- Duplicate and dependent rows do not invalidate full-rank Gram selection. -/
theorem dependent_equalities_singleton :
    optimizeRational (![![1],![-1],![2],![-2]] : Matrix (Fin 4) (Fin 1) ℚ)
      ![1/2,-1/2,1,-1] ![1] = some ![1/2] := by
  unfold optimizeRational rationalCandidateList activeSelections
  rw [Fin.sort_univ]
  decide +kernel

/-- Empty ambient dimension is handled by the determinant of the empty matrix. -/
theorem zero_dimensional_singleton :
    optimizeRational (fun i : Fin 0 => Fin.elim0 i : Matrix (Fin 0) (Fin 0) ℚ)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) = some (fun i => Fin.elim0 i) := by decide +kernel

end PermanssonResearch.ReverseSolver.ExactPolytope.Regression
