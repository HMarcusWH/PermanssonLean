import PermanssonResearch.ReverseSolver.CanonicalAllHorizonCorrespondence
import Mathlib.Tactic

/-!
# Lane C1 — exact rational reference matrix and finite hitting certificates

This is an independent certified four-state rational calculation. It does
NOT by itself prove that TypedStrategicWitness.model induces this matrix:
that identity is a separate alpha/P/U proof obligation.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactRationalAbsorption

open ReverseSolver

/-- Rows are in the order t=0, u=1, a=2, b=3. -/
def fourStateMatrix : RationalMarkovMatrix 4 where
  entry := fun y z =>
    if y = 0 then
      if z = 1 then 1 else 0
    else if y = 1 then
      if z = 1 then 1/2 else if z = 2 then 1/6
      else if z = 3 then 1/3 else 0
    else if z = y then 1 else 0
  entry_nonneg := by
    intro y z
    split_ifs <;> norm_num
  row_sum_one := by
    intro y
    fin_cases y <;> norm_num [Fin.sum_univ_four]

/-- Both absorbing destinations count as the same *hitting set*, while their
terminal identities remain different for the random-limit law. -/
def absorbingTarget : RationalHittingTarget 4 where
  goal := {2, 3}
  forbidden := ∅
  disjoint := by simp

/-- Two transitions from t give absorption probability exactly 1/2. -/
theorem t_two_step_hit :
    rationalHittingValue fourStateMatrix absorbingTarget 2 0 = 1/2 := by
  norm_num [rationalHittingValue, fourStateMatrix,
    absorbingTarget, Fin.sum_univ_four]

/-- Two transitions from u give absorption probability exactly 3/4. -/
theorem u_two_step_hit :
    rationalHittingValue fourStateMatrix absorbingTarget 2 1 = 3/4 := by
  norm_num [rationalHittingValue, fourStateMatrix,
    absorbingTarget, Fin.sum_univ_four]

/-- The absorbing starting states have success from time zero. -/
theorem a_initial_hit :
    rationalHittingValue fourStateMatrix absorbingTarget 0 2 = 1 := by
  norm_num [rationalHittingValue, absorbingTarget]

theorem b_initial_hit :
    rationalHittingValue fourStateMatrix absorbingTarget 0 3 = 1 := by
  norm_num [rationalHittingValue, absorbingTarget]


/-- The already-certified D0 correspondence transports the finite arithmetic
to the REAL canonical finite-prefix Markov path measure. -/
theorem canonical_t_two_step_hit :
    hittingValue (rationalTargetAsFrozen absorbingTarget)
      (rationalFiniteKernel fourStateMatrix) 0 2 = (1/2 : ℝ) := by
  rw [← rationalHittingValue_eq_canonical_all_horizons]
  norm_num [t_two_step_hit]

theorem canonical_u_two_step_hit :
    hittingValue (rationalTargetAsFrozen absorbingTarget)
      (rationalFiniteKernel fourStateMatrix) 1 2 = (3/4 : ℝ) := by
  rw [← rationalHittingValue_eq_canonical_all_horizons]
  norm_num [u_two_step_hit]

end ExactRationalAbsorption
end MultipleLimit
end PermanssonResearch
