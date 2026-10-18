import PermanssonResearch.MultipleLimit.CanonicalInitialAbsoluteContinuity
import PermanssonResearch.MultipleLimit.StationaryCanonicalShift
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! The complete canonical path-law change of initial distribution has
Radon--Nikodym density (dμ/dπ)(Y0). The actual trajectory kernel copies its
initial state; this gives equality of full measures directly, hence also
every finite-cylinder identity. No positive atoms or finite states are used. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultipleLimit.CanonicalInitial

set_option autoImplicit false
noncomputable section

theorem composition_withDensity {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    (κ : Kernel Y Ω) (π : Measure Y) (p : Ω → Y) (hp : Measurable p)
    (copy : ∀ y, ∀ᵐ w ∂κ y, p w = y) (f : Y → ℝ≥0∞) (hf : Measurable f) :
    κ ∘ₘ (π.withDensity f) = (κ ∘ₘ π).withDensity (f ∘ p) := by
  ext E hE
  rw [Measure.bind_apply hE κ.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul π hf (κ.measurable_coe hE),
    withDensity_apply _ hE, ← lintegral_indicator hE]
  rw [Measure.lintegral_bind κ.aemeasurable ((hf.comp hp).indicator hE).aemeasurable]
  apply lintegral_congr
  intro y
  calc
    f y * κ y E = ∫⁻ w, E.indicator (fun _ => f y) w ∂κ y := by simp [hE,mul_comm]
    _ = ∫⁻ w, E.indicator (f ∘ p) w ∂κ y := by
      apply lintegral_congr_ae
      filter_upwards [copy y] with w hw
      by_cases he : w ∈ E <;> simp [he,hw]

variable {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
open FiniteCanonicalPath StationaryCanonical

def pointPathKernel (K : Kernel Y Y) [IsMarkovKernel K] : Kernel Y (ℕ → Y) :=
  (Kernel.traj (fun n => PermanssonLean.ProbabilitySupport.stationaryPrefixKernel K n) 0).comap
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Y)).symm
    (MeasurableEquiv.measurable _)

instance pointPathKernel_isMarkov (K : Kernel Y Y) [IsMarkovKernel K] :
    IsMarkovKernel (pointPathKernel K) := by unfold pointPathKernel; infer_instance

theorem pointPathKernel_apply (K : Kernel Y Y) [IsMarkovKernel K] (y : Y) :
    pointPathKernel K y = canonicalPathLaw K (Measure.dirac y) := by
  rw [canonicalPathLaw_dirac_eq_traj]
  rfl

theorem pathLaw_eq_point_comp (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    canonicalPathLaw K μ = pointPathKernel K ∘ₘ μ := by
  ext E hE
  unfold canonicalPathLaw Kernel.trajMeasure
  rw [Measure.bind_apply hE (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hE) (MeasurableEquiv.measurable _),
    Measure.bind_apply hE (Kernel.aemeasurable _)]
  rfl

theorem pointPathKernel_initial (K : Kernel Y Y) [IsMarkovKernel K] (y : Y) :
    ∀ᵐ w ∂pointPathKernel K y, w 0 = y := by
  have he : ∀ᵐ z ∂(pointPathKernel K y).map (fun w : ℕ → Y => w 0), z = y := by
    rw [pointPathKernel_apply,canonical_eval_zero]
    simp
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable he

theorem pathLaw_eq_withDensity (K : Kernel Y Y) [IsMarkovKernel K]
    (μ π : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure π] (h : μ ≪ π) :
    canonicalPathLaw K μ = (canonicalPathLaw K π).withDensity
      (fun w : ℕ → Y => μ.rnDeriv π (w 0)) := by
  rw [pathLaw_eq_point_comp,pathLaw_eq_point_comp]
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ π h]
  exact composition_withDensity (pointPathKernel K) π (fun w => w 0) (measurable_pi_apply 0)
    (pointPathKernel_initial K) (μ.rnDeriv π) (Measure.measurable_rnDeriv μ π)

theorem pathLaw_rnDeriv (K : Kernel Y Y) [IsMarkovKernel K]
    (μ π : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure π] (h : μ ≪ π) :
    (canonicalPathLaw K μ).rnDeriv (canonicalPathLaw K π) =ᵐ[canonicalPathLaw K π]
      fun w : ℕ → Y => μ.rnDeriv π (w 0) := by
  rw [pathLaw_eq_withDensity K μ π h]
  exact Measure.rnDeriv_withDensity _ ((Measure.measurable_rnDeriv μ π).comp (measurable_pi_apply 0))

end
end PermanssonResearch.MultipleLimit.CanonicalInitial
