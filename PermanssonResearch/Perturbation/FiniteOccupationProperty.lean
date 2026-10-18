import PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
import PermanssonLean.Regime.ConstitutiveMargin
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
An occupation property fixed independently of every compared kernel.  Its
default probability is fixed before observing a path.  The finite C2 theorem
is used to identify this actual limit, rather than to define the observable.
-/

open Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology
namespace PermanssonResearch.Perturbation.FiniteOccupationProperty
open MultipleLimit MultipleLimit.FiniteStateOccupation
open MultipleLimit.FiniteCanonicalPath MultipleLimit.FiniteOccupationRandomLaw
open MultipleLimit.KernelCommunication MultipleLimit.RecurrentClassDecomposition
open MultipleLimit.CanonicalClassSelector MultipleLimit.ClassStationarySelectionLaw
set_option autoImplicit false

variable {Y V : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y]
variable [MetricSpace V] [MeasurableSpace V] [BorelSpace V] [Fintype V]

instance probability_completelyMetrizable :
    IsCompletelyMetrizableSpace (ProbabilityMeasure V) := by
  letI := TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure V)
  infer_instance

noncomputable def descriptorEmpirical (h : Y → V) (n : ℕ)
    (w : ℕ → Y) : ProbabilityMeasure V :=
  empiricalOccupation (fun t => h (w t)) (n+1) (Nat.succ_pos n)

theorem descriptorEmpirical_stronglyMeasurable (h : Y → V) (n : ℕ) :
    StronglyMeasurable (descriptorEmpirical h n) := by
  let F : (Fin (n+1) → Y) → ProbabilityMeasure V := fun p =>
    (PermanssonLean.RegimeSpecification.uniformFinProbability
      (n+1) (Nat.succ_pos n)).map (fun i => h (p i))
  have hf : StronglyMeasurable F := .of_discrete
  have hp : Measurable (fun w : ℕ → Y => fun i : Fin (n+1) => w i) :=
    Measurable.of_eval (fun i => measurable_pi_apply (i : ℕ))
  exact hf.comp_measurable hp

/-- This map depends only on the descriptor, normalization convention and
predeclared fallback law.  In particular it has no Markov-kernel parameter. -/
noncomputable def occupationLimit (h : Y → V) (fallback : ProbabilityMeasure V)
    (w : ℕ → Y) : ProbabilityMeasure V := by
  classical
  letI : Nonempty (ProbabilityMeasure V) := ⟨fallback⟩
  exact if ∃ q, Tendsto (fun n => descriptorEmpirical h n w) atTop (𝓝 q)
    then limUnder atTop (fun n => descriptorEmpirical h n w) else fallback

theorem occupationLimit_stronglyMeasurable (h : Y → V)
    (fallback : ProbabilityMeasure V) :
    StronglyMeasurable (occupationLimit h fallback) := by
  classical
  letI : Nonempty (ProbabilityMeasure V) := ⟨fallback⟩
  have hf := descriptorEmpirical_stronglyMeasurable h
  have hs := StronglyMeasurable.measurableSet_exists_tendsto (l := atTop) hf
  exact (StronglyMeasurable.limUnder hf).piecewise hs stronglyMeasurable_const

theorem occupationLimit_weakBorel_measurable (h : Y → V)
    (fallback : ProbabilityMeasure V) :
    @Measurable (ℕ → Y) (ProbabilityMeasure V) inferInstance (borel _)
      (occupationLimit h fallback) := by
  letI : MeasurableSpace (ProbabilityMeasure V) := borel _
  letI : BorelSpace (ProbabilityMeasure V) := ⟨rfl⟩
  exact (occupationLimit_stronglyMeasurable h fallback).measurable

theorem occupationLimit_default (h : Y → V) (fallback : ProbabilityMeasure V)
    (w : ℕ → Y)
    (hw : ¬ ∃ q, Tendsto (fun n => descriptorEmpirical h n w) atTop (𝓝 q)) :
    occupationLimit h fallback w = fallback := by
  classical
  exact if_neg hw

theorem occupationLimit_of_tendsto (h : Y → V) (fallback q : ProbabilityMeasure V)
    (w : ℕ → Y)
    (hw : Tendsto (fun n => descriptorEmpirical h n w) atTop (𝓝 q)) :
    occupationLimit h fallback w = q := by
  classical
  rw [occupationLimit, if_pos ⟨q,hw⟩, hw.limUnder_eq]

theorem descriptorEmpirical_eq_map (h : Y → V) (n : ℕ) (w : ℕ → Y) :
    descriptorEmpirical h n w =
      (empiricalOccupation w (n+1) (Nat.succ_pos n)).map h := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun i : Fin (n+1) => h (w (i : ℕ)))
      (PermanssonLean.RegimeSpecification.uniformFinProbability
        (n+1) (Nat.succ_pos n)).toMeasure =
    Measure.map h (Measure.map (fun i : Fin (n+1) => w (i : ℕ))
      (PermanssonLean.RegimeSpecification.uniformFinProbability
        (n+1) (Nat.succ_pos n)).toMeasure)
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  rfl

variable [Nonempty Y] [DecidableEq Y] [TopologicalSpace Y] [DiscreteTopology Y]
variable [OpensMeasurableSpace Y] [StandardBorelSpace Y]

/-- The one-recurrent-class hypothesis is about the actual finite kernel.
The stationary target is independently constructed by the existing C2
compactness and class uniqueness proofs. -/
theorem occupationLimit_ae_unique_class
    (K : Kernel Y Y) [IsMarkovKernel K]
    (C : Set Y) (hC : C ∈ RecurrentClasses K)
    (hunique : ∀ D ∈ RecurrentClasses K, D = C)
    (h : Y → V) (fallback : ProbabilityMeasure V) (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      occupationLimit h fallback w = (stationaryForSet K C).map h := by
  filter_upwards [observedOccupationLimit_ae_correct K μ h] with w hw
  have hc : CommunicatingClass K (selectedRepresentative K w) = C :=
    hunique _ ((recurrentClasses_mem_iff K _).2
      ⟨_, selectedRepresentative_recurrent K w, rfl⟩)
  apply occupationLimit_of_tendsto h fallback _ w
  simpa only [descriptorEmpirical_eq_map, observedOccupationLimit,
    physicalOccupationLimit, hc] using hw

/-- A real original full-path property, as an integral of a continuous
functional of the predeclared empirical-occupation limit. -/
noncomputable def property (h : Y → V) (fallback : ProbabilityMeasure V)
    (Φ : C(ProbabilityMeasure V, ℝ)) :
    PermanssonLean.RegimePropertyMap Y ℝ :=
  fun Λ => ∫ w, Φ (occupationLimit h fallback w) ∂Λ

theorem property_integrand_stronglyMeasurable (h : Y → V)
    (fallback : ProbabilityMeasure V) (Φ : C(ProbabilityMeasure V, ℝ)) :
    StronglyMeasurable (fun w => Φ (occupationLimit h fallback w)) :=
  Φ.continuous.comp_stronglyMeasurable (occupationLimit_stronglyMeasurable h fallback)

theorem property_integrand_integrable (h : Y → V)
    (fallback : ProbabilityMeasure V) (Φ : C(ProbabilityMeasure V, ℝ))
    (Λ : ProbabilityMeasure (ℕ → Y)) :
    Integrable (fun w => Φ (occupationLimit h fallback w)) Λ.toMeasure := by
  apply Integrable.of_bound
    (property_integrand_stronglyMeasurable h fallback Φ).aestronglyMeasurable
    ‖BoundedContinuousFunction.mkOfCompact Φ‖
  exact ae_of_all _ (fun w =>
    (BoundedContinuousFunction.mkOfCompact Φ).norm_coe_le_norm _)

theorem property_factor_unique_class
    (K : Kernel Y Y) [IsMarkovKernel K]
    (C : Set Y) (hC : C ∈ RecurrentClasses K)
    (hunique : ∀ D ∈ RecurrentClasses K, D = C)
    (h : Y → V) (fallback : ProbabilityMeasure V)
    (Φ : C(ProbabilityMeasure V, ℝ)) (μ : ProbabilityMeasure Y) :
    property h fallback Φ ⟨canonicalPathLaw K μ.toMeasure,inferInstance⟩ =
      Φ ((stationaryForSet K C).map h) := by
  have heq := occupationLimit_ae_unique_class K C hC hunique h fallback μ
  unfold property
  calc
    _ = ∫ _w, Φ ((stationaryForSet K C).map h)
        ∂canonicalPathLaw K μ.toMeasure := by
      apply integral_congr_ae
      filter_upwards [heq] with w hw
      exact congrArg Φ hw
    _ = _ := by simp

end PermanssonResearch.Perturbation.FiniteOccupationProperty
