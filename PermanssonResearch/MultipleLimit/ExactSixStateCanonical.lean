import PermanssonResearch.MultipleLimit.ExactSixStateQuotient
import PermanssonResearch.ReverseSolver.CanonicalAllHorizonCorrespondence
import Mathlib.Tactic

/-!
# Lane C2 — genuine finite-prefix canonical hitting for six-state model

Reuse the existing formally proven D0 rational-to-canonical finite-prefix
transport. The six-state matrix is a real Markov kernel through
`ReverseSolver.rationalFiniteKernel`. This file proves actual finite-prefix
hitting values for the class-union target, not merely arithmetic about an
unrelated simulated matrix.

The all-horizon, infinite-path almost-sure class-selection and occupation
laws remain separate, unproved C2 obligations.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateCanonical

open ExactSixState ReverseSolver

def sixStateMatrix : RationalMarkovMatrix 6 where
  entry := transition
  entry_nonneg := transition_nonneg
  row_sum_one := transition_row_sum

def recurrentTarget : RationalHittingTarget 6 where
  goal := {2, 3, 4, 5}
  forbidden := ∅
  disjoint := by simp

theorem t_two_step_hit :
    rationalHittingValue sixStateMatrix recurrentTarget 2 0 = 1/2 := by
  norm_num [rationalHittingValue, sixStateMatrix, recurrentTarget,
    transition, Fin.sum_univ_succ]

theorem u_two_step_hit :
    rationalHittingValue sixStateMatrix recurrentTarget 2 1 = 3/4 := by
  norm_num [rationalHittingValue, sixStateMatrix, recurrentTarget,
    transition, Fin.sum_univ_succ]

theorem two_step_hit_at_least_half (i : Fin 6) :
    (1/2 : ℚ) ≤ rationalHittingValue sixStateMatrix recurrentTarget 2 i := by
  fin_cases i <;> norm_num [rationalHittingValue, sixStateMatrix,
    recurrentTarget, transition, Fin.sum_univ_succ]

/-- The actual *canonical* finite-prefix probability of reaching the
union of both recurrent classes from t within two transitions is 1/2. -/
theorem canonical_t_two_step_hit :
    hittingValue (rationalTargetAsFrozen recurrentTarget)
      (rationalFiniteKernel sixStateMatrix) 0 2 = (1/2 : ℝ) := by
  rw [← rationalHittingValue_eq_canonical_all_horizons]
  norm_num [t_two_step_hit]

theorem canonical_u_two_step_hit :
    hittingValue (rationalTargetAsFrozen recurrentTarget)
      (rationalFiniteKernel sixStateMatrix) 1 2 = (3/4 : ℝ) := by
  rw [← rationalHittingValue_eq_canonical_all_horizons]
  norm_num [u_two_step_hit]

end ExactSixStateCanonical
end MultipleLimit
end PermanssonResearch
