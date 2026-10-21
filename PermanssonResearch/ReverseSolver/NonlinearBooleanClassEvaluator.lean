import PermanssonResearch.ReverseSolver.NonlinearPeriodThreeExpectedScore
import PermanssonResearch.ReverseSolver.StationaryOccupationObjective
import Mathlib.Tactic

/-!
Exact C11 class-evaluator adapter. It *requires* a certified rational
evaluation of every supported class; favorable numerical outputs alone
are never accepted as Lean proof.
-/
open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.ReverseSolver.NonlinearPeriodThree
open PermanssonResearch.ReverseSolver.StationaryOccupation
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonResearch.ReverseSolver.C10
open PermanssonResearch.ReverseSolver.C11
set_option autoImplicit false

noncomputable def booleanClassFunctionalFromCertifiedEvaluation
    {n : ℕ} [NeZero n]
    (h : PermanssonLean.JointState Unit (Fin n) → Bool)
    (evaluate : RationalMarkovMatrix n → Finset (Fin n) → ℚ)
    (hbounded : ∃ M : ℝ, ∀ ν : ProbabilityMeasure Bool,
      |booleanProbabilityScore ν| ≤ M)
    (hExact : ∀ (L : RationalMarkovMatrix n) (C : Finset (Fin n))
      (hC : C ∈ bottomClasses L),
      booleanProbabilityScore
        ((certifiedProbability L (referenceClassCandidate L C)
          (referenceClassCandidate_check L C hC)).map h) =
            (evaluate L C : ℝ)) :
    ExactClassFunctional n Bool where
  descriptor := h
  functional := booleanProbabilityScore
  bounded := hbounded
  evaluate := evaluate
  evaluate_exact := hExact

end PermanssonResearch.ReverseSolver.NonlinearPeriodThree
