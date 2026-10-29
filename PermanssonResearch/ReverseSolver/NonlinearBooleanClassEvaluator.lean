import PermanssonResearch.ReverseSolver.NonlinearPeriodThreeExpectedScore
import PermanssonResearch.ReverseSolver.StationaryOccupationObjective
import PermanssonResearch.ReverseSolver.C11ObservedStationary
import Mathlib.Tactic

/-!
# N3 — a REAL exact C11 Boolean nonlinear class evaluator

The original C11 certifiedProbability is built from actual checked rational
stationary vectors. The already-proved certified_true_mass identifies its
physical Bool descriptor mass with the same rational trueShare. Thus the
nonlinear class score is proved for EVERY rational Markov matrix and EVERY
C11 checked bottom class, not provided as an external hExact assumption.
The generic StationaryOccupationObjective.rationalObjective_eq_actual then
evaluates the original infinite canonical path law classwise.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace PermanssonResearch.ReverseSolver.NonlinearPeriodThree

open PermanssonLean
open PermanssonResearch.ReverseSolver.C11
open PermanssonResearch.ReverseSolver.C10
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonResearch.ReverseSolver.StationaryOccupation
open PermanssonResearch.ReverseSolver.NonlinearOccupationBoundary

set_option autoImplicit false

/-- Exact evaluation of the nonlinear Boolean score on a certified actual
C11 typed probability law. No stationary barycenter is substituted. -/
theorem certified_boolean_score_exact
    {n : ℕ} (L : RationalMarkovMatrix n)
    (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true)
    (h : Fin n → Bool) :
    booleanProbabilityScore
      ((certifiedProbability L r hc).map
        (fun y : JointState Unit (Fin n) => h (encode y))) =
      (booleanRationalScore (trueShare r h) : ℝ) := by
  have hmass :
      (((certifiedProbability L r hc).map
        (fun y : JointState Unit (Fin n) => h (encode y))).toMeasure
          ({true} : Set Bool)).toReal = (trueShare r h : ℝ) := by
    have hmassENN := certified_true_mass L r hc h
    have hMassMap :
        ((certifiedProbability L r hc).map
          (fun y : JointState Unit (Fin n) => h (encode y))).toMeasure
            ({true} : Set Bool) = ENNReal.ofReal (trueShare r h : ℝ) := by
      rw [ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton true)]
      simpa only [Set.preimage, Set.mem_setOf_eq, Set.mem_singleton_iff] using hmassENN
    rw [hMassMap]
    exact ENNReal.toReal_ofReal
      (by exact_mod_cast trueShare_nonneg L r hc h)
  unfold booleanProbabilityScore booleanRationalScore
    NonlinearOccupationBoundary.score
  rw [hmass]
  simp only [Rat.cast_sub, Rat.cast_abs, Rat.cast_one, Rat.cast_div,
    Rat.cast_ofNat]

/-- The actual score is uniformly bounded because Bool probabilities are
in [0,1]. This is proved from the original probability measure, not
postulated in the ExactClassFunctional interface. -/
theorem boolean_score_bounded :
    ∃ M : ℝ, ∀ ν : ProbabilityMeasure Bool,
      |booleanProbabilityScore ν| ≤ M := by
  refine ⟨1, ?_⟩
  intro ν
  have hmeas : ν.toMeasure ({true} : Set Bool) ≤ (1 : ℝ≥0∞) := by
    calc
      _ ≤ ν.toMeasure Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hmass0 : 0 ≤ (ν.toMeasure ({true} : Set Bool)).toReal :=
    ENNReal.toReal_nonneg
  have hmass1 : (ν.toMeasure ({true} : Set Bool)).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hmeas)
  have habs :
      |(ν.toMeasure ({true} : Set Bool)).toReal - (2/3 : ℝ)| ≤ 2/3 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hnonneg :
      0 ≤ 1 - |(ν.toMeasure ({true} : Set Bool)).toReal - (2/3 : ℝ)| := by
    linarith
  unfold booleanProbabilityScore
  rw [abs_of_nonneg hnonneg]
  linarith [abs_nonneg ((ν.toMeasure ({true} : Set Bool)).toReal - (2/3 : ℝ))]

/-- Concrete and uniform exact rational class evaluator for the Boolean
descriptor h. It does NOT assume a pre-proved evaluate_exact field. -/
noncomputable def booleanClassFunctional
    {n : ℕ} [NeZero n] (h : Fin n → Bool) :
    ExactClassFunctional n Bool where
  descriptor := fun y => h (encode y)
  functional := booleanProbabilityScore
  bounded := boolean_score_bounded
  evaluate := fun L C =>
    booleanRationalScore (trueShare (referenceClassCandidate L C) h)
  evaluate_exact := by
    intro L C hC
    exact certified_boolean_score_exact L
      (referenceClassCandidate L C)
      (referenceClassCandidate_check L C hC) h

/-- Full actual infinite-path occupation objective agrees with exact
classwise rational C11 evaluation, for every supported rational matrix. -/
theorem boolean_rational_objective_eq_actual
    {n : ℕ} [NeZero n] (h : Fin n → Bool)
    (L : RationalMarkovMatrix n) (y : Fin n) :
    ((rationalObjective (booleanClassFunctional h) L y : ℚ) : ℝ) =
      actualObjective (booleanClassFunctional h) L y :=
  rationalObjective_eq_actual (booleanClassFunctional h) L y

end PermanssonResearch.ReverseSolver.NonlinearPeriodThree
