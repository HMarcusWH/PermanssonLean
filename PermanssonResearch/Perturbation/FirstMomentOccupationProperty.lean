import PermanssonResearch.Probability.FirstMomentTopology
import PermanssonLean.Regime.ConstitutiveMargin

/-! A fixed global probability-valued occupation limit on the complete
first-moment space, with a predeclared default. The observable has no kernel
parameter. Actual empirical convergence is used to identify its value. -/

open MeasureTheory Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction

namespace PermanssonResearch.Perturbation.FirstMomentOccupation

open PermanssonResearch.Probability
set_option autoImplicit false

variable {Y V : Type*} [MeasurableSpace Y]
variable [MetricSpace V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SeparableSpace V]

noncomputable def descriptorEmpirical (v₀ : V) (h : Y → V) (n : ℕ) (w : ℕ → Y) :
    FirstMomentProbability v₀ := FirstMomentEmpirical.empirical v₀ n (fun t => h (w t))

theorem descriptorEmpirical_stronglyMeasurable (v₀ : V) {h : Y → V}
    (hh : Measurable h) (n : ℕ) : StronglyMeasurable (descriptorEmpirical v₀ h n) :=
  (FirstMomentEmpirical.empirical_stronglyMeasurable v₀ n).comp_measurable
    (Measurable.of_eval (fun t => hh.comp (measurable_pi_apply t)))

noncomputable def occupationLimit (v₀ : V) (h : Y → V) (fallback : FirstMomentProbability v₀)
    (w : ℕ → Y) : FirstMomentProbability v₀ := by
  classical
  letI : Nonempty (FirstMomentProbability v₀) := ⟨fallback⟩
  exact if ∃ ν, Tendsto (fun n => descriptorEmpirical v₀ h n w) atTop (𝓝 ν)
    then limUnder atTop (fun n => descriptorEmpirical v₀ h n w) else fallback

theorem occupationLimit_stronglyMeasurable (v₀ : V) {h : Y → V} (hh : Measurable h)
    (fallback : FirstMomentProbability v₀) : StronglyMeasurable (occupationLimit v₀ h fallback) := by
  classical
  letI : Nonempty (FirstMomentProbability v₀) := ⟨fallback⟩
  have hf := descriptorEmpirical_stronglyMeasurable v₀ hh
  exact (StronglyMeasurable.limUnder hf).piecewise
    (StronglyMeasurable.measurableSet_exists_tendsto (l := atTop) hf) stronglyMeasurable_const

/-- This is measurability of an actual probability-valued map for the Borel
sigma-algebra of the original weak probability topology. -/
theorem occupationLimit_probability_weakBorel_measurable (v₀ : V) {h : Y → V}
    (hh : Measurable h) (fallback : FirstMomentProbability v₀) :
    @Measurable (ℕ → Y) (ProbabilityMeasure V) inferInstance (borel (ProbabilityMeasure V))
      (fun w => (occupationLimit v₀ h fallback w).probability) := by
  letI : MeasurableSpace (ProbabilityMeasure V) := borel _
  letI : BorelSpace (ProbabilityMeasure V) := ⟨rfl⟩
  exact (FirstMomentProbability.probability_continuous.comp_stronglyMeasurable
    (occupationLimit_stronglyMeasurable v₀ hh fallback)).measurable

theorem occupationLimit_default (v₀ : V) (h : Y → V) (fallback : FirstMomentProbability v₀)
    (w : ℕ → Y) (hw : ¬ ∃ ν, Tendsto (fun n => descriptorEmpirical v₀ h n w) atTop (𝓝 ν)) :
    occupationLimit v₀ h fallback w = fallback := by
  classical
  exact if_neg hw

theorem occupationLimit_of_tendsto (v₀ : V) (h : Y → V)
    (fallback ν : FirstMomentProbability v₀) (w : ℕ → Y)
    (hw : Tendsto (fun n => descriptorEmpirical v₀ h n w) atTop (𝓝 ν)) :
    occupationLimit v₀ h fallback w = ν := by
  classical
  rw [occupationLimit, if_pos ⟨ν, hw⟩, hw.limUnder_eq]

noncomputable def property (v₀ : V) (h : Y → V) (fallback : FirstMomentProbability v₀)
    (Φ : FirstMomentProbability v₀ →ᵇ ℝ) : PermanssonLean.RegimePropertyMap Y ℝ :=
  fun Λ => ∫ w, Φ (occupationLimit v₀ h fallback w) ∂Λ.toMeasure

theorem property_integrand_integrable (v₀ : V) {h : Y → V} (hh : Measurable h)
    (fallback : FirstMomentProbability v₀) (Φ : FirstMomentProbability v₀ →ᵇ ℝ)
    (Λ : ProbabilityMeasure (ℕ → Y)) :
    Integrable (fun w => Φ (occupationLimit v₀ h fallback w)) Λ.toMeasure :=
  Integrable.of_bound (Φ.continuous.comp_stronglyMeasurable
    (occupationLimit_stronglyMeasurable v₀ hh fallback)).aestronglyMeasurable ‖Φ‖
      (ae_of_all _ (fun w => Φ.norm_coe_le_norm _))

theorem property_factor_of_ae_empirical_limit (v₀ : V) (h : Y → V)
    (fallback ν : FirstMomentProbability v₀) (Φ : FirstMomentProbability v₀ →ᵇ ℝ)
    (Λ : ProbabilityMeasure (ℕ → Y))
    (hlim : ∀ᵐ w ∂Λ.toMeasure,
      Tendsto (fun n => descriptorEmpirical v₀ h n w) atTop (𝓝 ν)) :
    property v₀ h fallback Φ Λ = Φ ν := by
  unfold property
  calc
    _ = ∫ _w, Φ ν ∂Λ.toMeasure := by
      apply integral_congr_ae
      filter_upwards [hlim] with w hw
      rw [occupationLimit_of_tendsto v₀ h fallback ν w hw]
    _ = _ := by simp

end PermanssonResearch.Perturbation.FirstMomentOccupation
