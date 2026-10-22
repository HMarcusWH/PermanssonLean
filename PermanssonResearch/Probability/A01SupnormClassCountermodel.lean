import PermanssonResearch.Probability.FiniteKantorovichDuality
import Mathlib.Tactic

/-!
# A-01: unit-supnorm is NOT the full bounded one-Lipschitz dual class

The two probability atoms 0 and 4 in the real line have a unit-Lipschitz
witness with value difference four, e.g. clamp(x,0,4), which is globally
bounded but NOT bounded in absolute value by one. Any test additionally
restricted to absolute values <= 1 at both atoms has a difference <= 2.
The original finite KR result uses the correctly typed test class; this
countermodel does not replace its actual coupling/duality theorem.
-/

namespace PermanssonResearch.Probability.A01SupnormClass
set_option autoImplicit false

def clipped (x : ℝ) : ℝ := max 0 (min x 4)

theorem clipped_lipschitz :
    LipschitzWith 1 clipped := by
  change LipschitzWith 1 (fun x : ℝ => max 0 (min x 4))
  exact (LipschitzWith.id.min_const (4 : ℝ)).const_max 0

theorem clipped_gap_four :
    |clipped 4 - clipped 0| = (4 : ℝ) := by
  norm_num [clipped]

theorem supnorm_one_gap_le_two (f : ℝ → ℝ)
    (h0 : |f 0| ≤ 1) (h4 : |f 4| ≤ 1) :
    |f 4 - f 0| ≤ (2 : ℝ) := by
  rcases abs_le.mp h0 with ⟨h0lo, h0hi⟩
  rcases abs_le.mp h4 with ⟨h4lo, h4hi⟩
  apply abs_le.mpr
  constructor <;> linarith

theorem no_unit_supnorm_witness_for_gap_four :
    ¬ ∃ f : ℝ → ℝ,
        |f 0| ≤ 1 ∧ |f 4| ≤ 1 ∧ (4 : ℝ) ≤ |f 4 - f 0| := by
  rintro ⟨f, h0, h4, hgap⟩
  have hb := supnorm_one_gap_le_two f h0 h4
  linarith

theorem legitimate_bounded_lipschitz_witness_not_unit_supnorm :
    LipschitzWith 1 clipped ∧
      |clipped 4 - clipped 0| = (4 : ℝ) ∧
      ¬ (∀ x : ℝ, |clipped x| ≤ 1) := by
  refine ⟨clipped_lipschitz, clipped_gap_four, ?_⟩
  intro hb
  have hh := hb 4
  norm_num [clipped] at hh

end PermanssonResearch.Probability.A01SupnormClass
