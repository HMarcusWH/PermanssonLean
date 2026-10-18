import PermanssonResearch.Perturbation.RegenerativeOccupationProperty
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! A literal probability-valued descriptor limit and fixed fallback law
for compact descriptors, alongside the general numeric limit observable. -/

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction
namespace PermanssonResearch.Perturbation.RegenerativeCompactOccupation
open MultipleLimit RegenerativeOccupationProperty
set_option autoImplicit false
variable {Y V : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SeparableSpace Y]
variable [MetricSpace V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V]

instance probability_completelyMetrizable :
    IsCompletelyMetrizableSpace (ProbabilityMeasure V) := by
  letI := TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure V)
  infer_instance

noncomputable def occupationLimit (h : Y → V) (fallback : ProbabilityMeasure V)
    (w : ℕ → Y) : ProbabilityMeasure V := by
  classical
  letI : Nonempty (ProbabilityMeasure V) := ⟨fallback⟩
  exact if ∃ ν, Tendsto (fun n => descriptorEmpirical h n w) atTop (𝓝 ν)
    then limUnder atTop (fun n => descriptorEmpirical h n w) else fallback

theorem descriptorEmpirical_stronglyMeasurable {h : Y → V} (hh : Continuous h) (n : ℕ) :
    StronglyMeasurable (descriptorEmpirical h n) := by
  letI : MeasurableSpace (ProbabilityMeasure V) := borel _
  letI : BorelSpace (ProbabilityMeasure V) := ⟨rfl⟩
  exact (descriptorEmpirical_continuous hh n).measurable.stronglyMeasurable

theorem occupationLimit_stronglyMeasurable {h : Y → V} (hh : Continuous h)
    (fallback : ProbabilityMeasure V) : StronglyMeasurable (occupationLimit h fallback) := by
  classical
  letI : Nonempty (ProbabilityMeasure V) := ⟨fallback⟩
  have hf := descriptorEmpirical_stronglyMeasurable hh
  exact (StronglyMeasurable.limUnder hf).piecewise
    (StronglyMeasurable.measurableSet_exists_tendsto (l := atTop) hf) stronglyMeasurable_const

theorem occupationLimit_default (h : Y → V) (fallback : ProbabilityMeasure V) (w : ℕ → Y)
    (hw : ¬ ∃ ν, Tendsto (fun n => descriptorEmpirical h n w) atTop (𝓝 ν)) :
    occupationLimit h fallback w = fallback := by
  classical
  exact if_neg hw

theorem occupationLimit_of_tendsto (h : Y → V) (fallback ν : ProbabilityMeasure V)
    (w : ℕ → Y) (hw : Tendsto (fun n => descriptorEmpirical h n w) atTop (𝓝 ν)) :
    occupationLimit h fallback w = ν := by
  classical
  rw [occupationLimit,if_pos ⟨ν,hw⟩,hw.limUnder_eq]

theorem numericLimit_eq_functional_lawLimit (h : Y → V) (fallback ν : ProbabilityMeasure V)
    (Φ : ProbabilityMeasure V →ᵇ ℝ) (w : ℕ → Y)
    (hw : Tendsto (fun n => descriptorEmpirical h n w) atTop (𝓝 ν)) :
    numericLimit h fallback Φ w = Φ (occupationLimit h fallback w) := by
  rw [numericLimit_of_descriptor_tendsto h fallback ν Φ w hw,
    occupationLimit_of_tendsto h fallback ν w hw]

noncomputable def property (h : Y → V) (fallback : ProbabilityMeasure V)
    (Φ : ProbabilityMeasure V →ᵇ ℝ) : PermanssonLean.RegimePropertyMap Y ℝ :=
  fun Λ => ∫ w, Φ (occupationLimit h fallback w) ∂Λ.toMeasure

theorem property_integrand_integrable {h : Y → V} (hh : Continuous h)
    (fallback : ProbabilityMeasure V) (Φ : ProbabilityMeasure V →ᵇ ℝ)
    (Λ : ProbabilityMeasure (ℕ → Y)) :
    Integrable (fun w => Φ (occupationLimit h fallback w)) Λ.toMeasure :=
  Integrable.of_bound (Φ.continuous.comp_stronglyMeasurable
    (occupationLimit_stronglyMeasurable hh fallback)).aestronglyMeasurable ‖Φ‖
      (ae_of_all _ fun w => Φ.norm_coe_le_norm _)

variable [StandardBorelSpace Y] [Nonempty Y]

theorem occupationLimit_ae_regenerative (K R : Kernel Y Y) [IsMarkovKernel K] [IsMarkovKernel R]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : Probability.Regenerative.IsMixture R K ξ r) {h : Y → V} (hh : Continuous h)
    (fallback : ProbabilityMeasure V) :
    ∀ᵐ w ∂FiniteCanonicalPath.canonicalPathLaw K μ.toMeasure,
      occupationLimit h fallback w = (Probability.Regenerative.probabilityLaw R ξ hr hr1).map h := by
  filter_upwards [MultipleLimit.Regenerative.canonical_regenerative_empirical K R ξ μ hr hr1 hmix]
    with w hw
  apply occupationLimit_of_tendsto
  simpa only [descriptorEmpirical_eq_map hh] using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hw hh

theorem property_factor_regenerative (K R : Kernel Y Y) [IsMarkovKernel K] [IsMarkovKernel R]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : Probability.Regenerative.IsMixture R K ξ r) {h : Y → V} (hh : Continuous h)
    (fallback : ProbabilityMeasure V) (Φ : ProbabilityMeasure V →ᵇ ℝ) :
    property h fallback Φ ⟨FiniteCanonicalPath.canonicalPathLaw K μ.toMeasure,inferInstance⟩ =
      Φ ((Probability.Regenerative.probabilityLaw R ξ hr hr1).map h) := by
  unfold property
  have heq := occupationLimit_ae_regenerative K R ξ μ hr hr1 hmix hh fallback
  calc
    _ = ∫ _w, Φ ((Probability.Regenerative.probabilityLaw R ξ hr hr1).map h)
        ∂FiniteCanonicalPath.canonicalPathLaw K μ.toMeasure := by
      apply integral_congr_ae
      filter_upwards [heq] with w hw
      exact congrArg Φ hw
    _ = _ := by simp

end PermanssonResearch.Perturbation.RegenerativeCompactOccupation
