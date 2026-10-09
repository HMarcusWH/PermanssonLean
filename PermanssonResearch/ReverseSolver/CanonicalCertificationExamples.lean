import PermanssonResearch.ReverseSolver.CanonicalAllHorizonCorrespondence
import PermanssonResearch.ReverseSolver.CertificationExamples
import Mathlib.Tactic

/-!
# D0-C: concrete canonical hitting-value regressions

These exercise the actual mathlib `finitePrefixLaw` via the universal
D0-C theorem on certified two-state rational matrices.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace CanonicalExamples

/-- Being in the goal at time zero succeeds without a transition. -/
theorem goal_at_time_zero :
    hittingValue (rationalTargetAsFrozen RationalExamples.goalOne)
      (rationalFiniteKernel RationalExamples.halfGoalMatrix)
      (1 : Fin 2) 0 = 1 := by
  rw [← rationalHittingValue_eq_canonical_all_horizons]
  norm_num [rationalHittingValue, RationalExamples.goalOne]

/-- One step in the half-goal matrix gives exactly one-half goal mass. -/
theorem half_goal_one_step :
    hittingValue (rationalTargetAsFrozen RationalExamples.goalOne)
      (rationalFiniteKernel RationalExamples.halfGoalMatrix)
      (0 : Fin 2) 1 = (1 / 2 : ℝ) := by
  rw [← rationalHittingValue_eq_canonical_all_horizons]
  norm_num [rationalHittingValue, RationalExamples.halfGoalMatrix,
    RationalExamples.goalOne, Fin.sum_univ_two]

/-- Two genuine transitions (no phantom step at zero) give three quarters. -/
theorem half_goal_two_steps :
    hittingValue (rationalTargetAsFrozen RationalExamples.goalOne)
      (rationalFiniteKernel RationalExamples.halfGoalMatrix)
      (0 : Fin 2) 2 = (3 / 4 : ℝ) := by
  rw [← rationalHittingValue_eq_canonical_all_horizons]
  norm_num [rationalHittingValue, RationalExamples.halfGoalMatrix,
    RationalExamples.goalOne, Fin.sum_univ_two]

def goalOneForbiddenZero : RationalHittingTarget 2 where
  goal := {1}
  forbidden := {0}
  disjoint := by decide

/-- Starting in forbidden state fails even if the kernel would move to goal. -/
theorem forbidden_at_time_zero :
    hittingValue (rationalTargetAsFrozen goalOneForbiddenZero)
      (rationalFiniteKernel RationalExamples.sureGoalMatrix)
      (0 : Fin 2) 1 = 0 := by
  rw [← rationalHittingValue_eq_canonical_all_horizons]
  norm_num [rationalHittingValue, goalOneForbiddenZero]

/-- The certification theorem is uniform in horizon and initial state. -/
theorem half_goal_all_horizons (T : ℕ) (y : Fin 2) :
    hittingValue (rationalTargetAsFrozen RationalExamples.goalOne)
      (rationalFiniteKernel RationalExamples.halfGoalMatrix) y T =
    (rationalHittingValue RationalExamples.halfGoalMatrix
      RationalExamples.goalOne T y : ℝ) :=
  (rationalHittingValue_eq_canonical_all_horizons
    RationalExamples.halfGoalMatrix RationalExamples.goalOne T y).symm

end CanonicalExamples
end ReverseSolver
end PermanssonResearch
