import PermanssonResearch.ReverseSolver.NonlinearPeriodThreeCanonical
import PermanssonResearch.ReverseSolver.NonlinearOccupationBoundaryFixture
import Mathlib.Tactic

/-!
NEXT-06.2 nonlinear Boolean occupation functional on the genuine native
two-valued physical world. The same classwise score must be evaluated
before averaging over distinct recurrent classes; a stationary barycenter
cannot in general be passed into this nonlinear functional.
-/
open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.ReverseSolver.NonlinearPeriodThree

open PermanssonResearch.ReverseSolver.NonlinearOccupationBoundary

/-- Actual fixed nonlinear score of a physical Bool occupation probability.
The functional acts on a probability law, not on a mean law from hidden classes. -/
noncomputable def booleanProbabilityScore (ν : ProbabilityMeasure Bool) : ℝ :=
  1 - |(ν.toMeasure {true}).toReal - (2/3 : ℝ)|

/-- A class certified to have true occupation 2/3 gets objective one. -/
theorem boolean_probability_score_of_true_mass
    (ν : ProbabilityMeasure Bool)
    (h : (ν.toMeasure {true}).toReal = (2/3 : ℝ)) :
    booleanProbabilityScore ν = 1 := by
  simp [booleanProbabilityScore, h]

/-- A reusable exact rational evaluator for any class with rational Boolean
true mass p in [0,1]. This does not purport to identify p for a C11 matrix. -/
def booleanRationalScore (p : ℚ) : ℚ :=
  NonlinearOccupationBoundary.score p

theorem boolean_rational_score_bounds (p : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ booleanRationalScore p ∧ booleanRationalScore p ≤ 1 := by
  have hl : -(1 : ℚ) ≤ p - 2/3 := by linarith
  have hr : p - 2/3 ≤ (1 : ℚ) := by linarith
  have hval : |p - 2/3| ≤ (1 : ℚ) := abs_le.mpr ⟨hl,hr⟩
  constructor
  · dsimp [booleanRationalScore, NonlinearOccupationBoundary.score]
    linarith
  · dsimp [booleanRationalScore, NonlinearOccupationBoundary.score]
    linarith [abs_nonneg (p - 2/3)]

/-- Two distinct absorbing physical classes, half weight each: aggregate
CLASS scores gives 1/2 but nonlinear score of barycenter gives 5/6. -/
theorem classwise_barycenter_invalid :
    ((booleanRationalScore 0 + booleanRationalScore 1)/2 = (1/2 : ℚ)) ∧
    (booleanRationalScore (1/2) = (5/6 : ℚ)) := by
  constructor <;> norm_num [booleanRationalScore, NonlinearOccupationBoundary.score]

/-- A probability p=2/3 is an algebraic randomized-policy tie boundary;
its realization as an actual randomized canonical occupation requires
its own model-specific probability proof. -/
theorem randomized_tie_score : booleanRationalScore (2/3) = 1 := by
  norm_num [booleanRationalScore, NonlinearOccupationBoundary.score]

end PermanssonResearch.ReverseSolver.NonlinearPeriodThree
