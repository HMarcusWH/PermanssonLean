import PermanssonResearch.X1.Parameters

/-! # X1: exact Bellman and one-shot incentive certificates for BOTH players

The `pRep` used here defines the actual world kernel (`world_replete`). These
finite discounted one-shot conditions are certified for each indexed player;
the general infinite-history discounted policy verification theorem is a
separate open bridge, not silently assumed by this module.
-/

namespace PermanssonResearch.X1

set_option autoImplicit false

def continuation (i : Player) (x : Bool) (a : Action) : ℚ :=
  pRep x a * value i true + (1 - pRep x a) * value i false

def deviationValue (i : Player) (x ai : Bool) : ℚ :=
  piAction x false * (reward i x (deviationAction i ai false) +
    discount * continuation i x (deviationAction i ai false)) +
  piAction x true * (reward i x (deviationAction i ai true) +
    discount * continuation i x (deviationAction i ai true))

/-- V20.35 for every indexed player, with the full independent joint policy. -/
theorem bellman_equation (i : Player) (x : Bool) :
    value i x = ∑ a : Action, piAction x a.1 * piAction x a.2 *
      (reward i x a + discount * continuation i x a) := by
  fin_cases i <;> cases x <;>
    norm_num [Fintype.sum_prod_type, sum_bool, piAction, piExtract, boolMass,
      value, reward, ownAction, otherAction, indicator, continuation, pRep,
      discount, congestion, depletionCost]

/-- V20.36 for BOTH players, BOTH world states and EVERY pure deviation. -/
theorem no_pure_deviation (i : Player) (x ai : Bool) :
    deviationValue i x ai ≤ value i x := by
  fin_cases i <;> cases x <;> cases ai <;>
    norm_num [deviationValue, deviationAction, piAction, piExtract, boolMass,
      value, reward, ownAction, otherAction, indicator, continuation, pRep,
      discount, congestion, depletionCost]

/-- Equality on every positive-support action for BOTH players. -/
theorem support_equality (i : Player) (x ai : Bool) (h : piAction x ai ≠ 0) :
    deviationValue i x ai = value i x := by
  fin_cases i <;> cases x <;> cases ai <;>
    simp_all [deviationValue, deviationAction, piAction, piExtract, boolMass,
      value, reward, ownAction, otherAction, indicator, continuation, pRep,
      discount, congestion, depletionCost] <;> norm_num

/-- Every mixed one-shot unilateral deviation is a convex combination of the
certified pure deviations. The quantifier is all rational p in [0,1]. -/
theorem no_mixed_deviation (i : Player) (x : Bool) (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (1-p) * deviationValue i x false + p * deviationValue i x true ≤ value i x := by
  calc
    _ ≤ (1-p) * value i x + p * value i x :=
      add_le_add (mul_le_mul_of_nonneg_left (no_pure_deviation i x false)
        (sub_nonneg.mpr hp.2))
        (mul_le_mul_of_nonneg_left (no_pure_deviation i x true) hp.1)
    _ = value i x := by ring

/-- The same certificate covers ALL real-valued Boolean mixed deviations,
not only alternatives with rational probabilities. -/
theorem no_real_mixed_deviation (i : Player) (x : Bool) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    (1-p) * (deviationValue i x false : ℝ) + p * (deviationValue i x true : ℝ) ≤
      (value i x : ℝ) := by
  have hfalse : (deviationValue i x false : ℝ) ≤ (value i x : ℝ) := by
    exact_mod_cast no_pure_deviation i x false
  have htrue : (deviationValue i x true : ℝ) ≤ (value i x : ℝ) := by
    exact_mod_cast no_pure_deviation i x true
  calc
    _ ≤ (1-p) * (value i x : ℝ) + p * (value i x : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hfalse (sub_nonneg.mpr hp.2))
        (mul_le_mul_of_nonneg_left htrue hp.1)
    _ = (value i x : ℝ) := by ring

theorem depleted_strict (i : Player) :
    deviationValue i false true < deviationValue i false false := by
  fin_cases i <;>
    norm_num [deviationValue, deviationAction, piAction, piExtract, boolMass,
      value, reward, ownAction, otherAction, indicator, continuation, pRep,
      discount, congestion, depletionCost]

end PermanssonResearch.X1
