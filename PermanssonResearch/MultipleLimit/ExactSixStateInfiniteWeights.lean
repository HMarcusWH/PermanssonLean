import PermanssonResearch.MultipleLimit.ExactSixStateEndpointEvents
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# C53-14 — true infinite-path 1/3 and 2/3 class hitting probabilities

Exact finite-prefix class-A/B hit mass for the canonical alpha/P/U
six-state chain is (1/3 or 2/3)·(1-2^-T) from transient u,
and the same with a one-step shift from transient t.

Monotone continuity of the INFINITE path measure converts these into
precise probabilities of ever entering each physical recurrent class.
This is not yet equated with the canonical class selector until the
independently proved a.s. eventual residence is used downstream.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateInfiniteWeights

open ReverseSolver.FiniteStrategicRealization
open ExactSixStateTyped
open ExactSixStateEndpointRecurrences
open ExactSixStateEndpointEvents

private theorem half_to_zero :
    Tendsto (fun n : ℕ => (1/2 : ℝ)^n)
      atTop (𝓝 (0 : ℝ)) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

private theorem cast_hitA_u (T : ℕ) :
    (typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6)))).real
      (hitA T) =
      (1/3 : ℝ) * (1 - (1/2 : ℝ)^T) := by
  convert typed_hitA_real (1 : Fin 6) T using 1 <;>
    simp [hitA_from_u_closed]

private theorem cast_hitB_u (T : ℕ) :
    (typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6)))).real
      (hitB T) =
      (2/3 : ℝ) * (1 - (1/2 : ℝ)^T) := by
  convert typed_hitB_real (1 : Fin 6) T using 1 <;>
    simp [hitB_from_u_closed]

theorem ever_hit_A_u :
    typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6)))
      (⋃ T : ℕ, hitA T) = ENNReal.ofReal (1/3 : ℝ) := by
  let P := typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6)))
  have hR : Tendsto (fun T : ℕ => P.real (hitA T))
      atTop (𝓝 (1/3 : ℝ)) := by
    have hOne : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
    have h := (hOne.sub half_to_zero).const_mul (1/3 : ℝ)
    convert h using 1
    · funext T
      exact cast_hitA_u T
    · norm_num
  have hE : Tendsto (fun T : ℕ => P (hitA T))
      atTop (𝓝 (ENNReal.ofReal (1/3 : ℝ))) := by
    have h := ENNReal.tendsto_ofReal hR
    have hcon (T : ℕ) :
        ENNReal.ofReal (P.real (hitA T)) = P (hitA T) :=
      ENNReal.ofReal_toReal (measure_ne_top P (hitA T))
    simpa only [hcon] using h
  have hcont : Tendsto (fun T : ℕ => P (hitA T))
      atTop (𝓝 (P (⋃ T : ℕ, hitA T))) :=
    tendsto_measure_iUnion_atTop (μ := P) hitA_monotone
  exact tendsto_nhds_unique hcont hE

theorem ever_hit_B_u :
    typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6)))
      (⋃ T : ℕ, hitB T) = ENNReal.ofReal (2/3 : ℝ) := by
  let P := typedModel.pathLaw (Measure.dirac (decode (1 : Fin 6)))
  have hR : Tendsto (fun T : ℕ => P.real (hitB T))
      atTop (𝓝 (2/3 : ℝ)) := by
    have hOne : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
    have h := (hOne.sub half_to_zero).const_mul (2/3 : ℝ)
    convert h using 1
    · funext T
      exact cast_hitB_u T
    · norm_num
  have hE : Tendsto (fun T : ℕ => P (hitB T))
      atTop (𝓝 (ENNReal.ofReal (2/3 : ℝ))) := by
    have h := ENNReal.tendsto_ofReal hR
    have hcon (T : ℕ) :
        ENNReal.ofReal (P.real (hitB T)) = P (hitB T) :=
      ENNReal.ofReal_toReal (measure_ne_top P (hitB T))
    simpa only [hcon] using h
  have hcont : Tendsto (fun T : ℕ => P (hitB T))
      atTop (𝓝 (P (⋃ T : ℕ, hitB T))) :=
    tendsto_measure_iUnion_atTop (μ := P) hitB_monotone
  exact tendsto_nhds_unique hcont hE

theorem shifted_hitA_union :
    (⋃ T : ℕ, hitA (T+1)) = (⋃ T : ℕ, hitA T) := by
  ext w
  constructor
  · rintro ⟨T,hT⟩
    exact Set.mem_iUnion.mpr ⟨T+1,hT⟩
  · rintro ⟨T,hT⟩
    exact Set.mem_iUnion.mpr
      ⟨T,hitA_monotone (Nat.le_succ T) hT⟩

theorem shifted_hitB_union :
    (⋃ T : ℕ, hitB (T+1)) = (⋃ T : ℕ, hitB T) := by
  ext w
  constructor
  · rintro ⟨T,hT⟩
    exact Set.mem_iUnion.mpr ⟨T+1,hT⟩
  · rintro ⟨T,hT⟩
    exact Set.mem_iUnion.mpr
      ⟨T,hitB_monotone (Nat.le_succ T) hT⟩

private theorem cast_hitA_t (T : ℕ) :
    (typedModel.pathLaw (Measure.dirac (decode (0 : Fin 6)))).real
      (hitA (T+1)) =
      (1/3 : ℝ) * (1 - (1/2 : ℝ)^T) := by
  convert typed_hitA_real (0 : Fin 6) (T+1) using 1 <;>
    simp [hitA_from_t_closed]

private theorem cast_hitB_t (T : ℕ) :
    (typedModel.pathLaw (Measure.dirac (decode (0 : Fin 6)))).real
      (hitB (T+1)) =
      (2/3 : ℝ) * (1 - (1/2 : ℝ)^T) := by
  convert typed_hitB_real (0 : Fin 6) (T+1) using 1 <;>
    simp [hitB_from_t_closed]

theorem ever_hit_A_t :
    typedModel.pathLaw (Measure.dirac (decode (0 : Fin 6)))
      (⋃ T : ℕ, hitA T) = ENNReal.ofReal (1/3 : ℝ) := by
  let P := typedModel.pathLaw (Measure.dirac (decode (0 : Fin 6)))
  have hR : Tendsto (fun T : ℕ => P.real (hitA (T+1)))
      atTop (𝓝 (1/3 : ℝ)) := by
    have hOne : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
    have h := (hOne.sub half_to_zero).const_mul (1/3 : ℝ)
    convert h using 1
    · funext T
      exact cast_hitA_t T
    · norm_num
  have hE : Tendsto (fun T : ℕ => P (hitA (T+1)))
      atTop (𝓝 (ENNReal.ofReal (1/3 : ℝ))) := by
    have h := ENNReal.tendsto_ofReal hR
    have hcon (T : ℕ) :
        ENNReal.ofReal (P.real (hitA (T+1))) =
          P (hitA (T+1)) :=
      ENNReal.ofReal_toReal (measure_ne_top P (hitA (T+1)))
    simpa only [hcon] using h
  have hm : Monotone (fun T : ℕ => hitA (T+1)) := by
    intro m n hmn
    exact hitA_monotone (Nat.succ_le_succ hmn)
  have hcont : Tendsto (fun T : ℕ => P (hitA (T+1)))
      atTop (𝓝 (P (⋃ T : ℕ, hitA (T+1)))) :=
    tendsto_measure_iUnion_atTop (μ := P) hm
  rw [shifted_hitA_union] at hcont
  exact tendsto_nhds_unique hcont hE

theorem ever_hit_B_t :
    typedModel.pathLaw (Measure.dirac (decode (0 : Fin 6)))
      (⋃ T : ℕ, hitB T) = ENNReal.ofReal (2/3 : ℝ) := by
  let P := typedModel.pathLaw (Measure.dirac (decode (0 : Fin 6)))
  have hR : Tendsto (fun T : ℕ => P.real (hitB (T+1)))
      atTop (𝓝 (2/3 : ℝ)) := by
    have hOne : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
    have h := (hOne.sub half_to_zero).const_mul (2/3 : ℝ)
    convert h using 1
    · funext T
      exact cast_hitB_t T
    · norm_num
  have hE : Tendsto (fun T : ℕ => P (hitB (T+1)))
      atTop (𝓝 (ENNReal.ofReal (2/3 : ℝ))) := by
    have h := ENNReal.tendsto_ofReal hR
    have hcon (T : ℕ) :
        ENNReal.ofReal (P.real (hitB (T+1))) =
          P (hitB (T+1)) :=
      ENNReal.ofReal_toReal (measure_ne_top P (hitB (T+1)))
    simpa only [hcon] using h
  have hm : Monotone (fun T : ℕ => hitB (T+1)) := by
    intro m n hmn
    exact hitB_monotone (Nat.succ_le_succ hmn)
  have hcont : Tendsto (fun T : ℕ => P (hitB (T+1)))
      atTop (𝓝 (P (⋃ T : ℕ, hitB (T+1)))) :=
    tendsto_measure_iUnion_atTop (μ := P) hm
  rw [shifted_hitB_union] at hcont
  exact tendsto_nhds_unique hcont hE

end ExactSixStateInfiniteWeights
end MultipleLimit
end PermanssonResearch
