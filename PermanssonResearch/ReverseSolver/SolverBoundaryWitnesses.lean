import Mathlib.Tactic

/-!
# Exact separation witnesses for distinct solver information structures

These are required boundary regressions. They do not assert LP completeness,
robust-history optimality or an infinite-safety synthesis theorem.
-/

namespace PermanssonResearch.ReverseSolver.SolverBoundaryWitnesses

/-- The stated hard-risk budget limits the risky mixing probability to one half. -/
theorem hard_risk_budget_forces_half (p : ℚ) (hbudget : p/10≤1/20) : p≤1/2 := by
  linarith

theorem hard_risk_success_upper (p : ℚ) (hbudget : p/10≤1/20) :
    4/5+p/10≤17/20 := by linarith

theorem hard_risk_half_mixture_attains :
    ((1/2 : ℚ)/10=1/20) ∧ (4/5+(1/2 : ℚ)/10=17/20) ∧
      ¬((1 : ℚ)/10≤1/20) := by norm_num

/-- When nature sees a private-draw distribution, matching/opposite rewards
give `min p (1-p)` and mixing attains one half. -/
theorem private_draw_matching_upper (p : ℚ) : min p (1-p)≤1/2 := by
  by_cases hp : p≤1/2
  · exact le_trans (min_le_left _ _) hp
  · exact le_trans (min_le_right _ _) (by linarith)

theorem private_draw_matching_half_attains : min (1/2 : ℚ) (1-1/2)=1/2 := by norm_num

/-- If nature sees the realized choice, each pure choice has a zero row. -/
theorem realized_draw_matching_value_zero :
    max (min (1 : ℚ) 0) (min 0 1)=0 ∧
      max (min (1 : ℚ) 0) (min 0 1)<min (1/2 : ℚ) (1-1/2) := by norm_num

/-- A model committed for the whole horizon cannot choose its low-survival
row independently at each stage. -/
theorem whole_model_commitment_strictly_exceeds_rectangular :
    min ((1/10 : ℚ)*(9/10)) ((9/10 : ℚ)*(1/10))=9/100 ∧
    min (1/10 : ℚ) (9/10)*min (9/10 : ℚ) (1/10)=1/100 ∧
    (1/100 : ℚ)<9/100 := by norm_num

end PermanssonResearch.ReverseSolver.SolverBoundaryWitnesses
