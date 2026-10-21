import PermanssonResearch.Quotient.DiscountedCanonicalMarginClosure
import PermanssonResearch.Quotient.DiscountedOriginalMarginExamples
import Mathlib.Tactic

/-!
Exact discounted arithmetic adversaries. These facts inspect literal
closed-form model-output envelopes. They do not establish Exact GR or
identify the physical source kernels for an arbitrary outside model.
-/
namespace PermanssonResearch.Quotient.DiscountedCanonicalWitnessExamples
open PermanssonResearch.Quotient.DiscountedOriginalMarginExamples
open PermanssonResearch.Probability

theorem correct_frozen_discounted_budget :
    (∑' n : ℕ, (1-(1/3:ℝ))*(1/3:ℝ)^n*
      (1-(1-(1/5:ℝ))*(1-(1/4:ℝ))^n)) = 13/45 :=
  exact_thirteen_fortyfive_budget

/-- A well-formed but wrong rational literal cannot be substituted for the
true stationary discounted defect bound. -/
theorem wrong_frozen_discounted_budget :
    (∑' n : ℕ, (1-(1/3:ℝ))*(1/3:ℝ)^n*
      (1-(1-(1/5:ℝ))*(1-(1/4:ℝ))^n)) ≠ 14/45 := by
  rw [correct_frozen_discounted_budget]
  norm_num

end PermanssonResearch.Quotient.DiscountedCanonicalWitnessExamples
