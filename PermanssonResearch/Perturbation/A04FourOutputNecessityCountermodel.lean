import PermanssonResearch.Perturbation.FiniteOccupationFactorization
import Mathlib.Tactic

/-!
# A-04: no general three-output substitute for a four-process margin

For an original constitutive comparison, the baseline and intervention each
have an actual property output. Perturbing the model adds both of those
outputs separately. If one suppresses the perturbed intervention output,
three scalar numbers do not determine the margin difference.

This is a necessary-input countermodel to the *form* of the original
four-process wrapper; it is not an instantiation of the full typed canonical
path-law factorization theorem. That still requires its own source receipt.
-/

namespace PermanssonResearch.Perturbation.A04FourOutputNecessity
set_option autoImplicit false

def marginDifference (base treated perturbedBase perturbedTreated : ℝ) : ℝ :=
  dist (|perturbedBase - perturbedTreated|) (|base - treated|)

theorem same_three_outputs_different_true_margins :
    marginDifference 0 1 0 0 = (1 : ℝ) ∧
    marginDifference 0 1 0 1 = (0 : ℝ) := by
  constructor <;> norm_num [marginDifference, Real.dist_eq]

/-- No function of only the original baseline, original treatment, and
perturbed baseline outputs can return the correct margin difference for
every possible perturbed treatment output. -/
theorem no_general_three_output_margin_formula :
    ¬ ∃ f : ℝ → ℝ → ℝ → ℝ,
      ∀ base treated perturbedBase perturbedTreated : ℝ,
        f base treated perturbedBase =
          marginDifference base treated perturbedBase perturbedTreated := by
  rintro ⟨f, hf⟩
  have h0 := hf 0 1 0 0
  have h1 := hf 0 1 0 1
  norm_num [marginDifference, Real.dist_eq] at h0 h1
  linarith

end PermanssonResearch.Perturbation.A04FourOutputNecessity
