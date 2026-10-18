import PermanssonResearch.MultipleLimit.StationaryCanonicalShift
import PermanssonResearch.MultipleLimit.CanonicalInitialDensity
import PermanssonResearch.Probability.RegenerativeMeasure
import PermanssonResearch.Probability.EventTVCalculus

/-! The actual homogeneous canonical law after an arbitrary deterministic
time shift, without a stationary initial distribution. Changing the initial
law contracts whole-path event TV through the genuine trajectory kernel. -/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ProbabilityTheory
namespace PermanssonResearch.MultipleLimit.CanonicalShift
open FiniteCanonicalPath StationaryCanonical
open PermanssonLean.ProbabilitySupport PermanssonResearch.Probability
set_option autoImplicit false
variable {Y : Type*} [MeasurableSpace Y]

theorem prefix_zero_eq_map_eval (ρ : Measure (ℕ → Y)) :
    ρ.map (Preorder.frestrictLe 0) = (ρ.map (fun w => w 0)).map
      (MeasurableEquiv.piUnique (fun _ : Iic 0 => Y)).symm := by
  have he := (MeasurableEquiv.piUnique (fun _ : Iic 0 => Y)).symm.measurable
  rw [Measure.map_map he (measurable_pi_apply 0)]
  congr 1
  funext w i
  have hi : i.1 = 0 := Nat.le_zero.mp (mem_Iic.mp i.2)
  simp [hi]

theorem shift_law (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    (canonicalPathLaw K μ).map shift = canonicalPathLaw K (K ∘ₘ μ) := by
  have h0 : ((canonicalPathLaw K μ).map shift).map (fun w : ℕ → Y => w 0) =
      (canonicalPathLaw K (K ∘ₘ μ)).map (fun w => w 0) := by
    rw [Measure.map_map (measurable_pi_apply 0) measurable_shift]
    change (canonicalPathLaw K μ).map (fun w => w (0+1)) = _
    rw [CanonicalKernelMarginals.canonical_eval_succ,canonical_eval_zero,canonical_eval_zero]
  apply measure_eq_of_prefix_maps
  apply prefix_maps_eq K
  · rw [prefix_zero_eq_map_eval,prefix_zero_eq_map_eval,h0]
  · exact shifted_transition K μ
  · exact CanonicalKernelMarginals.canonical_transition_pair K (K ∘ₘ μ)

theorem iterated_shift_law (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : ProbabilityMeasure Y) (n : ℕ) :
    (canonicalPathLaw K μ.toMeasure).map (shift^[n]) =
      canonicalPathLaw K (Regenerative.orbitLaw K μ n) := by
  induction n with
  | zero => simp [Regenerative.orbitLaw]
  | succ n ih =>
    rw [Function.iterate_succ',← Measure.map_map measurable_shift (measurable_shift.iterate n),
      ih,shift_law]
    rfl

theorem kernel_comp_tv_le {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (κ : Kernel A B) [IsMarkovKernel κ]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    eventTotalVariation (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ eventTotalVariation μ ν := by
  have h := eventTotalVariation_map_le (μ ⊗ₘ κ) (ν ⊗ₘ κ) measurable_snd
  change eventTotalVariation (μ ⊗ₘ κ).snd (ν ⊗ₘ κ).snd ≤ _ at h
  rw [Measure.snd_compProd,Measure.snd_compProd] at h
  exact h.trans (eventTotalVariation_compProd_left_le μ ν κ)

theorem canonical_tv_le_initial [MeasurableSingletonClass Y]
    (K : Kernel Y Y) [IsMarkovKernel K]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    eventTotalVariation (canonicalPathLaw K μ) (canonicalPathLaw K ν) ≤
      eventTotalVariation μ ν := by
  rw [CanonicalInitial.pathLaw_eq_point_comp,CanonicalInitial.pathLaw_eq_point_comp]
  exact kernel_comp_tv_le _ μ ν

end PermanssonResearch.MultipleLimit.CanonicalShift
