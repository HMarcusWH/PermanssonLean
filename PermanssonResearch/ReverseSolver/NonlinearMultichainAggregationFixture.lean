import PermanssonResearch.ReverseSolver.NonlinearBooleanClassFunctional
import PermanssonResearch.ReverseSolver.C11ReferenceExamples
import PermanssonResearch.ReverseSolver.NonlinearBooleanClassEvaluator
import PermanssonResearch.MultipleLimit.FiniteCanonicalPath
import Mathlib.Tactic

/-!
D-09 independent physical-class identity and nonlinear-aggregation
negative fixture. These two statements are individually proved in the
existing C11/Boolean sources. The additional actual mixed-class entry-law
proof remains mandatory for full D-09 acceptance.
-/
namespace PermanssonResearch.ReverseSolver.NonlinearMultichainAggregationFixture
open PermanssonResearch.ReverseSolver.C11
open PermanssonResearch.ReverseSolver.C11.ReferenceExamples
open PermanssonResearch.ReverseSolver.NonlinearPeriodThree

theorem physically_distinct_classes_with_shared_descriptor :
    (referenceStationaryFamily twoAbsorbing).length = 2 ∧
      (referenceStationaryFamily twoAbsorbing).map (fun r =>
        ∑ x : Fin 2, r.weights x *
          (if (fun _ : Fin 2 => true) x then 1 else 0)) = [1,1] := by
  exact physical_classes_remain_distinct

theorem nonlinear_classwise_aggregation_not_barycenter :
    ((booleanRationalScore 0 + booleanRationalScore 1)/2 = (1/2:ℚ)) ∧
      (booleanRationalScore (1/2) = (5/6:ℚ)) :=
  classwise_barycenter_invalid


open MeasureTheory ProbabilityTheory
open PermanssonLean
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonResearch.ReverseSolver.StationaryOccupation

/-- The *genuine* typed alpha-P-U infinite canonical path law on a finite
world is affine in its initial probability. This is the existing generic
Ionescu-Tulcea mixture, not an assumed two-state probability table. -/
theorem actual_two_absorbing_full_path_mixture
    (μ : ProbabilityMeasure (JointState Unit (Fin 2))) :
    (realizedModel twoAbsorbing).pathLaw μ.toMeasure =
      ∑ y : JointState Unit (Fin 2),
        μ.toMeasure {y} •
          (realizedModel twoAbsorbing).pathLaw (Measure.dirac y) := by
  letI : IsMarkovKernel (realizedModel twoAbsorbing).inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov _
  calc
    (realizedModel twoAbsorbing).pathLaw μ.toMeasure =
        canonicalPathLaw (realizedModel twoAbsorbing).inducedKernel μ.toMeasure :=
      typed_pathLaw_eq_canonical (realizedModel twoAbsorbing) μ.toMeasure
    _ = ∑ y : JointState Unit (Fin 2),
          μ.toMeasure {y} •
            canonicalPathLaw (realizedModel twoAbsorbing).inducedKernel
              (Measure.dirac y) :=
      canonicalPathLaw_initial_mixture
        (realizedModel twoAbsorbing).inducedKernel μ
    _ = ∑ y : JointState Unit (Fin 2),
          μ.toMeasure {y} •
            (realizedModel twoAbsorbing).pathLaw (Measure.dirac y) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [typed_pathLaw_eq_canonical (realizedModel twoAbsorbing)
        (Measure.dirac y)]

/-- The descriptor distinguishes the two actual physical absorbing
classes, independently of the constant-descriptor class-identity test. -/
def observedPhysicalBool (x : Fin 2) : Bool := x == 1

/-- Exact rational endpoint scores for the real two-absorbing-class matrix.
This is computable C11 class arithmetic, not a polynomial score table
assumed to represent arbitrary external strategic-world models. -/
theorem exact_two_absorbing_rational_scores :
    rationalObjective (booleanClassFunctional observedPhysicalBool)
        twoAbsorbing (0 : Fin 2) = (1/3 : ℚ) ∧
    rationalObjective (booleanClassFunctional observedPhysicalBool)
        twoAbsorbing (1 : Fin 2) = (2/3 : ℚ) := by
  constructor <;> decide +kernel

/-- The arithmetic mean of the two ORIGINAL point-started infinite-path
expected nonlinear class scores equals one half. The full mixed initial
canonical path law is separately identified above, so this average is the
independent classwise decomposition, not score of the stationary barycenter. -/
theorem actual_equal_weight_original_scores :
    ((actualObjective (booleanClassFunctional observedPhysicalBool)
        twoAbsorbing (0 : Fin 2) +
       actualObjective (booleanClassFunctional observedPhysicalBool)
        twoAbsorbing (1 : Fin 2)) / 2) = (1/2 : ℝ) := by
  have h0 := boolean_rational_objective_eq_actual
    observedPhysicalBool twoAbsorbing (0 : Fin 2)
  have h1 := boolean_rational_objective_eq_actual
    observedPhysicalBool twoAbsorbing (1 : Fin 2)
  rw [← h0, ← h1]
  rcases exact_two_absorbing_rational_scores with ⟨hzero, hone⟩
  norm_num [hzero, hone]

theorem actual_multichain_classwise_differs_from_barycenter :
    ((actualObjective (booleanClassFunctional observedPhysicalBool)
        twoAbsorbing (0 : Fin 2) +
       actualObjective (booleanClassFunctional observedPhysicalBool)
        twoAbsorbing (1 : Fin 2)) / 2) ≠
      ((booleanRationalScore (1/2 : ℚ) : ℚ) : ℝ) := by
  rw [actual_equal_weight_original_scores]
  norm_num [booleanRationalScore, NonlinearOccupationBoundary.score]

end PermanssonResearch.ReverseSolver.NonlinearMultichainAggregationFixture
