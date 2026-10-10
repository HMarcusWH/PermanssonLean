import PermanssonResearch.MultipleLimit.AbsorbingFamily
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Lane C1 — quantitative uniform block-tail induction

For a Markov process, the missing stochastic-semigroup bridge is an
explicit N-step conditional survival bound. This file proves the exact
geometric induction **from that block-step inequality**, without replacing
it with a false unconditional independence assertion. The separate
kernel-to-block-step theorem is required before asserting generic
almost-sure hitting from an N-step kernel bound.
-/

open Filter

namespace PermanssonResearch
namespace MultipleLimit

/-- Abstract measurable survival-mass sequence at successive N-blocks.
The block-step inequality must be established from the actual kernel
before instantiating this object. -/
structure BlockSurvivalBound where
  survival : ℕ → ℝ
  epsilon : ℝ
  eps_pos : 0 < epsilon
  eps_le_one : epsilon ≤ 1
  survival_nonneg : ∀ k, 0 ≤ survival k
  survival_initial : survival 0 ≤ 1
  block_step : ∀ k, survival (k + 1) ≤ (1 - epsilon) * survival k

/-- The core uniform geometric survival estimate. -/
theorem BlockSurvivalBound.geometric_tail (B : BlockSurvivalBound) :
    ∀ k : ℕ, B.survival k ≤ (1 - B.epsilon) ^ k := by
  intro k
  induction k with
  | zero =>
      simpa using B.survival_initial
  | succ k ih =>
      have hq : 0 ≤ 1 - B.epsilon := sub_nonneg.mpr B.eps_le_one
      calc
        B.survival (k + 1) ≤ (1 - B.epsilon) * B.survival k :=
          B.block_step k
        _ ≤ (1 - B.epsilon) * (1 - B.epsilon) ^ k :=
          mul_le_mul_of_nonneg_left ih hq
        _ = (1 - B.epsilon) ^ (k + 1) := by ring

/-- As a consequence, the N-block survival probability goes to zero
with no assumption that successive blocks are independent. -/
theorem BlockSurvivalBound.survival_tendsto_zero
    (B : BlockSurvivalBound) :
    Tendsto B.survival atTop (𝓝 (0 : ℝ)) := by
  have hq0 : 0 ≤ 1 - B.epsilon := sub_nonneg.mpr B.eps_le_one
  have hq1 : 1 - B.epsilon < 1 := by linarith [B.eps_pos]
  have hp : Tendsto (fun k : ℕ => (1 - B.epsilon) ^ k)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  exact squeeze_zero (fun k => B.survival_nonneg k)
    B.geometric_tail hp

end MultipleLimit
end PermanssonResearch
