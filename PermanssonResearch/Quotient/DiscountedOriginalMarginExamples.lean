import PermanssonResearch.Quotient.DiscountedOriginalMargin
import PermanssonResearch.Probability.DiscountedInitialBudget
import Mathlib.Tactic

/-! NEXT-04 exact numerical budget and non-vacuous margin diagnostics.
Pure finite arithmetic never stands in for the source-bound whole-path theorem. -/
namespace PermanssonResearch.Quotient.DiscountedOriginalMargin

/-- Uniform initial mismatch epsilon=1/5 and row defect eta=1/4 under
discount beta=1/3 gives exactly the frozen 13/45 envelope. -/
theorem exact_thirteen_fortyfive_budget :
    (∑' n : ℕ, (1-(1/3:ℝ))*(1/3:ℝ)^n*
      (1-(1-(1/5:ℝ))*(1-(1/4:ℝ))^n)) = 13/45 := by
  rw [PermanssonResearch.Probability.discounted_geometric_budget_initial
    (show 0 ≤ (1/3:ℝ) by norm_num)
    (show (1/3:ℝ) < 1 by norm_num)
    (show 0 ≤ (1/4:ℝ) by norm_num)
    (show (1/4:ℝ) ≤ 1 by norm_num)]
  norm_num

/-- A nonzero reporting mismatch is never erased by a perfect model bridge. -/
theorem reporting_error_cannot_be_ignored :
    ¬ (∀ reported : ℝ, |reported - (0:ℝ)| ≤ 0) := by
  intro h
  have hh := h 1
  norm_num at hh

/-- Removing a smallest comparison effect changes the infimum.
This exact finite arithmetic is deliberately NOT a regime certificate. -/
theorem dropping_a_smallest_comparison_effect_changes_minimum :
    min (0:ℝ) 1 ≠ (1:ℝ) := by norm_num

end PermanssonResearch.Quotient.DiscountedOriginalMargin
