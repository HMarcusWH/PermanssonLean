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
open PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
open scoped ENNReal
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


/-- The original typed model's induced kernel is Markov; this supplies the
actual infinite-path occupation interface, without any replacement model. -/
noncomputable instance original_two_absorbing_induced_isMarkov :
    IsMarkovKernel (realizedModel twoAbsorbing).inducedKernel :=
  StrategicWorldModel.inducedKernel_isMarkov _

/-- The nonlinear integrand acts on the true infinite canonical path and
evaluates its selected physical stationary class, not the stationary
barycenter of a pair of point starts. -/
noncomputable def actualNonlinearPathScore
    (w : ℕ → JointState Unit (Fin 2)) : ℝ :=
  (booleanClassFunctional observedPhysicalBool).functional
    (observedOccupationLimit
      (realizedModel twoAbsorbing).inducedKernel
      (booleanClassFunctional observedPhysicalBool).descriptor w)

theorem actualNonlinearPathScore_integrable
    (y : JointState Unit (Fin 2)) :
    Integrable actualNonlinearPathScore
      ((realizedModel twoAbsorbing).pathLaw (Measure.dirac y)) := by
  rcases y with ⟨s, x⟩
  cases s
  -- The established integrability theorem uses the explicit occupation
  -- integrand and the decoded canonical initial state.  Both are
  -- definitionally the very same objects in the original full-path claim.
  change Integrable
    (fun w : ℕ → JointState Unit (Fin 2) =>
      (booleanClassFunctional observedPhysicalBool).functional
        (observedOccupationLimit
          (realizedModel twoAbsorbing).inducedKernel
          (booleanClassFunctional observedPhysicalBool).descriptor w))
    ((realizedModel twoAbsorbing).pathLaw (Measure.dirac (decode x)))
  exact occupation_functional_integrable
    (booleanClassFunctional observedPhysicalBool) twoAbsorbing x

/-- Genuine initial-source-to-entire-path integration for every mixed law.
The finite affine decomposition follows from the ORIGINAL typed canonical
path law, not a separately stipulated probability distribution. -/
theorem actual_mixed_initial_nonlinear_expectation
    (μ : ProbabilityMeasure (JointState Unit (Fin 2))) :
    (∫ w, actualNonlinearPathScore w
      ∂(realizedModel twoAbsorbing).pathLaw μ.toMeasure) =
      ∑ y : JointState Unit (Fin 2),
        (μ.toMeasure {y}).toReal *
          (∫ w, actualNonlinearPathScore w
            ∂(realizedModel twoAbsorbing).pathLaw (Measure.dirac y)) := by
  rw [actual_two_absorbing_full_path_mixture μ]
  have hint (y : JointState Unit (Fin 2)) :
      Integrable actualNonlinearPathScore
        (μ.toMeasure {y} •
          (realizedModel twoAbsorbing).pathLaw (Measure.dirac y)) := by
    have hle : μ.toMeasure {y} ≤ μ.toMeasure Set.univ :=
      measure_mono (Set.subset_univ _)
    have htop : μ.toMeasure {y} ≠ ⊤ := by
      rw [measure_univ] at hle
      have hone : (1 : ℝ≥0∞) ≠ ⊤ := by norm_num
      exact ne_top_of_le_ne_top hone hle
    exact (actualNonlinearPathScore_integrable y).smul_measure htop
  have h := integral_finsetSum_measure
    (s := (Finset.univ : Finset (JointState Unit (Fin 2))))
    (f := actualNonlinearPathScore)
    (μ := fun y => μ.toMeasure {y} •
      (realizedModel twoAbsorbing).pathLaw (Measure.dirac y))
    (by intro y _; exact hint y)
  simpa only [integral_smul_measure, smul_eq_mul] using h

/-- The fifty-fifty initial law is explicitly a genuine probability measure
on the original TWO PHYSICAL absorbing states. -/
noncomputable def equalWeightInitialLaw :
    ProbabilityMeasure (JointState Unit (Fin 2)) :=
  ⟨(ENNReal.ofReal (1/2 : ℝ) • Measure.dirac (decode (0 : Fin 2))) +
      (ENNReal.ofReal (1/2 : ℝ) • Measure.dirac (decode (1 : Fin 2))), by
    constructor
    have hh : ENNReal.ofReal (1/2 : ℝ) +
        ENNReal.ofReal (1/2 : ℝ) = 1 := by
      rw [← ENNReal.ofReal_add
        (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (0 : ℝ) ≤ 1/2)]
      norm_num
    simpa [Measure.add_apply, Measure.smul_apply] using hh⟩

theorem equalWeightInitialLaw_singleton (y : JointState Unit (Fin 2)) :
    (equalWeightInitialLaw.toMeasure {y}).toReal = (1/2 : ℝ) := by
  rcases y with ⟨s, x⟩
  cases s
  fin_cases x <;>
    norm_num [equalWeightInitialLaw, decode,
      Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']

/-- The single mixed-initial ORIGINAL infinite path law produces a classwise
mean. This is not evaluating F on an averaged descriptor law. -/
theorem actual_equal_mixture_original_nonlinear_score :
    (∫ w, actualNonlinearPathScore w
      ∂(realizedModel twoAbsorbing).pathLaw equalWeightInitialLaw.toMeasure) =
      (actualObjective (booleanClassFunctional observedPhysicalBool)
        twoAbsorbing (0 : Fin 2) +
       actualObjective (booleanClassFunctional observedPhysicalBool)
        twoAbsorbing (1 : Fin 2)) / 2 := by
  rw [actual_mixed_initial_nonlinear_expectation]
  -- The full path-law sum uses the original decoded joint states;
  -- normalize PUnit.unit/Bool pairs to those exact decoded sources before
  -- linear real algebra.  Nothing about the nonlinear score is replaced.
  simp [Fintype.sum_prod_type, Fin.sum_univ_two,
    equalWeightInitialLaw_singleton, actualNonlinearPathScore,
    actualObjective, decode] <;> ring

/-- Exact mixed-initial score one-half, unequal to scoring the barycenter
five-sixths; the constant-descriptor class-identity control remains separate. -/
theorem actual_mixed_nonlinear_half_not_barycenter :
    (∫ w, actualNonlinearPathScore w
      ∂(realizedModel twoAbsorbing).pathLaw equalWeightInitialLaw.toMeasure) =
        (1/2 : ℝ) ∧
    (∫ w, actualNonlinearPathScore w
      ∂(realizedModel twoAbsorbing).pathLaw equalWeightInitialLaw.toMeasure) ≠
        ((booleanRationalScore (1/2 : ℚ) : ℚ) : ℝ) := by
  constructor
  · rw [actual_equal_mixture_original_nonlinear_score]
    exact actual_equal_weight_original_scores
  · rw [actual_equal_mixture_original_nonlinear_score]
    exact actual_multichain_classwise_differs_from_barycenter

end PermanssonResearch.ReverseSolver.NonlinearMultichainAggregationFixture
