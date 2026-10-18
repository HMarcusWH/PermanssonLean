import PermanssonResearch.MultipleLimit.RegenerativeWeakEmpirical
import PermanssonLean.Regime.ConstitutiveMargin
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! A predeclared full-path numeric occupation observable, independent of
every kernel. Its fixed default is the functional of a fixed fallback law. -/

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction
namespace PermanssonResearch.Perturbation.RegenerativeOccupationProperty
open MultipleLimit MultipleLimit.FiniteStateOccupation
set_option autoImplicit false
variable {Y V : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SeparableSpace Y]
variable [MetricSpace V] [MeasurableSpace V] [BorelSpace V] [SeparableSpace V]

noncomputable def descriptorEmpirical (h : Y → V) (n : ℕ) (w : ℕ → Y) :
    ProbabilityMeasure V := empiricalOccupation (fun t => h (w t)) (n+1) (Nat.succ_pos n)

theorem descriptorEmpirical_continuous {h : Y → V} (hh : Continuous h) (n : ℕ) :
    Continuous (descriptorEmpirical h n) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.2
  intro f
  change Continuous (fun w : ℕ → Y => ∫ y, f y ∂(empiricalOccupation
    (fun t => h (w t)) (n+1) (Nat.succ_pos n)).toMeasure)
  simp_rw [MultipleLimit.Regenerative.empirical_integral _ n f f.continuous.measurable]
  exact (continuous_finset_sum _ (fun t _ => f.continuous.comp
    (hh.comp (continuous_apply t)))).div_const _

noncomputable def numericLimit (h : Y → V) (fallback : ProbabilityMeasure V)
    (Φ : ProbabilityMeasure V →ᵇ ℝ) (w : ℕ → Y) : ℝ := by
  classical
  exact if ∃ a, Tendsto (fun n => Φ (descriptorEmpirical h n w)) atTop (𝓝 a)
    then limUnder atTop (fun n => Φ (descriptorEmpirical h n w)) else Φ fallback

theorem numericLimit_default (h : Y → V) (fallback : ProbabilityMeasure V)
    (Φ : ProbabilityMeasure V →ᵇ ℝ) (w : ℕ → Y)
    (hw : ¬ ∃ a, Tendsto (fun n => Φ (descriptorEmpirical h n w)) atTop (𝓝 a)) :
    numericLimit h fallback Φ w = Φ fallback := by
  classical
  exact if_neg hw

theorem numericLimit_stronglyMeasurable {h : Y → V} (hh : Continuous h)
    (fallback : ProbabilityMeasure V) (Φ : ProbabilityMeasure V →ᵇ ℝ) :
    StronglyMeasurable (numericLimit h fallback Φ) := by
  classical
  have hf (n : ℕ) : StronglyMeasurable (fun w : ℕ → Y => Φ (descriptorEmpirical h n w)) :=
    (Φ.continuous.comp (descriptorEmpirical_continuous hh n)).measurable.stronglyMeasurable
  exact (StronglyMeasurable.limUnder hf).piecewise
    (StronglyMeasurable.measurableSet_exists_tendsto (l := atTop) hf) stronglyMeasurable_const

theorem numericLimit_of_descriptor_tendsto (h : Y → V) (fallback ν : ProbabilityMeasure V)
    (Φ : ProbabilityMeasure V →ᵇ ℝ) (w : ℕ → Y)
    (hw : Tendsto (fun n => descriptorEmpirical h n w) atTop (𝓝 ν)) :
    numericLimit h fallback Φ w = Φ ν := by
  classical
  have ht := Φ.continuous.continuousAt.tendsto.comp hw
  rw [numericLimit,if_pos ⟨Φ ν,ht⟩]
  exact ht.limUnder_eq

theorem numericLimit_abs_bound (h : Y → V) (fallback : ProbabilityMeasure V)
    (Φ : ProbabilityMeasure V →ᵇ ℝ) (w : ℕ → Y) : |numericLimit h fallback Φ w| ≤ ‖Φ‖ := by
  classical
  by_cases hc : ∃ a, Tendsto (fun n => Φ (descriptorEmpirical h n w)) atTop (𝓝 a)
  · obtain ⟨a,ha⟩ := hc
    rw [numericLimit,if_pos ⟨a,ha⟩,ha.limUnder_eq]
    apply le_of_tendsto' (continuous_abs.continuousAt.tendsto.comp ha)
    intro n
    simpa only [Function.comp_apply,Real.norm_eq_abs] using!
      Φ.norm_coe_le_norm (descriptorEmpirical h n w)
  · rw [numericLimit,if_neg hc]
    simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm fallback

noncomputable def property (h : Y → V) (fallback : ProbabilityMeasure V)
    (Φ : ProbabilityMeasure V →ᵇ ℝ) : PermanssonLean.RegimePropertyMap Y ℝ :=
  fun Λ => ∫ w, numericLimit h fallback Φ w ∂Λ.toMeasure

theorem property_integrand_integrable {h : Y → V} (hh : Continuous h)
    (fallback : ProbabilityMeasure V) (Φ : ProbabilityMeasure V →ᵇ ℝ)
    (Λ : ProbabilityMeasure (ℕ → Y)) : Integrable (numericLimit h fallback Φ) Λ.toMeasure :=
  Integrable.of_bound (numericLimit_stronglyMeasurable hh fallback Φ).aestronglyMeasurable ‖Φ‖
    (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using numericLimit_abs_bound h fallback Φ w)

theorem descriptorEmpirical_eq_map {h : Y → V} (hh : Continuous h) (n : ℕ) (w : ℕ → Y) :
    descriptorEmpirical h n w = (empiricalOccupation w (n+1) (Nat.succ_pos n)).map h := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun i : Fin (n+1) => h (w (i : ℕ)))
      (PermanssonLean.RegimeSpecification.uniformFinProbability (n+1) (Nat.succ_pos n)).toMeasure =
    Measure.map h (Measure.map (fun i : Fin (n+1) => w (i : ℕ))
      (PermanssonLean.RegimeSpecification.uniformFinProbability (n+1) (Nat.succ_pos n)).toMeasure)
  rw [Measure.map_map hh.measurable (measurable_of_finite _)]
  rfl

variable [StandardBorelSpace Y] [Nonempty Y]

theorem property_factor_regenerative (K R : Kernel Y Y) [IsMarkovKernel K] [IsMarkovKernel R]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : Probability.Regenerative.IsMixture R K ξ r)
    {h : Y → V} (hh : Continuous h) (fallback : ProbabilityMeasure V)
    (Φ : ProbabilityMeasure V →ᵇ ℝ) :
    property h fallback Φ ⟨FiniteCanonicalPath.canonicalPathLaw K μ.toMeasure,inferInstance⟩ =
      Φ ((Probability.Regenerative.probabilityLaw R ξ hr hr1).map h) := by
  have hae := MultipleLimit.Regenerative.canonical_regenerative_empirical K R ξ μ hr hr1 hmix
  have heq : ∀ᵐ w ∂FiniteCanonicalPath.canonicalPathLaw K μ.toMeasure,
      numericLimit h fallback Φ w = Φ ((Probability.Regenerative.probabilityLaw R ξ hr hr1).map h) := by
    filter_upwards [hae] with w hw
    apply numericLimit_of_descriptor_tendsto
    simpa only [descriptorEmpirical_eq_map hh] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hw hh
  unfold property
  calc
    _ = ∫ _w, Φ ((Probability.Regenerative.probabilityLaw R ξ hr hr1).map h)
        ∂FiniteCanonicalPath.canonicalPathLaw K μ.toMeasure := integral_congr_ae heq
    _ = _ := by simp

end PermanssonResearch.Perturbation.RegenerativeOccupationProperty
