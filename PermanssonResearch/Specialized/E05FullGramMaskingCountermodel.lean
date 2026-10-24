import PermanssonResearch.Specialized.GramSeparation
import Mathlib.Tactic

/-!
# E-05: source-bound Gram negative witness with a masking positive component

The frozen Gram witness of the ORIGINAL inner-product-space construction has
negative signed component when c>0 and Gram gap>0. This does not imply the
entire form remains negative after a separately budgeted summand is added.

An additional positive component 2*c*gap² exceeds the negative
-c*gap² signed term. The resulting total is STRICTLY POSITIVE on the
same genuine witness and with the same nondegenerate positive-gap premise.
No unqualified full-form negativity or empirical identification is claimed.
-/

namespace PermanssonResearch.Specialized.E05FullGramMaskingCountermodel

open PermanssonResearch.Specialized
open scoped InnerProductSpace
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A positive-gap source direction is exactly where the signed Gram
summand is strictly negative, yet its admissible additive budget matters. -/
theorem added_component_masks_actual_negative_gram
    {c : ℝ} (hc : 0 < c) (x y : E)
    (hgap : 0 < gramGap x y) :
    0 <
      c * (⟪x, gramWitness x y⟫_ℝ ^ 2 -
           ⟪y, gramWitness x y⟫_ℝ ^ 2) +
      2 * c * (gramGap x y) ^ 2 := by
  rw [signedGram_witness_value]
  have hpos : 0 < c * gramGap x y ^ 2 :=
    mul_pos hc (sq_pos_of_pos hgap)
  nlinarith

/-- The same hypotheses imply the negative signed Gram term. Both facts
coexist: the signed summand is negative but the displayed total is positive. -/
theorem original_signed_negative_but_total_positive
    {c : ℝ} (hc : 0 < c) (x y : E)
    (hgap : 0 < gramGap x y) :
    (c * (⟪x, gramWitness x y⟫_ℝ ^ 2 -
          ⟪y, gramWitness x y⟫_ℝ ^ 2) < 0) ∧
    (0 <
      c * (⟪x, gramWitness x y⟫_ℝ ^ 2 -
           ⟪y, gramWitness x y⟫_ℝ ^ 2) +
      2 * c * gramGap x y ^ 2) := by
  exact ⟨signedGram_witness_negative hc x y hgap,
    added_component_masks_actual_negative_gram hc x y hgap⟩

/-- The original quantitative budget cannot simply be dropped. -/
theorem extra_component_exceeds_negative_budget
    {c : ℝ} (hc : 0 < c) (x y : E)
    (hgap : 0 < gramGap x y) :
    ¬ (2 * c * gramGap x y ^ 2 < c * gramGap x y ^ 2) := by
  have hp : 0 < c * gramGap x y ^ 2 :=
    mul_pos hc (sq_pos_of_pos hgap)
  nlinarith

end PermanssonResearch.Specialized.E05FullGramMaskingCountermodel
