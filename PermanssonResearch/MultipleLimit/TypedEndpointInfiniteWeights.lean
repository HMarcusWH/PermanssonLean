import PermanssonResearch.MultipleLimit.TypedEndpointEvents
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Lane C1 — exact infinite-horizon absorption-destination visit weights

The finite-horizon probabilities were certified using the actual
canonical alpha/P/U path law and a separate objective for each absorbing
destination. Monotone continuity of a measurable increasing union then
gives the exact probability of ever visiting each destination.
No assumed independent trials or postulated endpoint distribution.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedEndpointInfiniteWeights

open TypedStrategicWitness TypedEndpointHitting TypedEndpointEvents

private theorem half_to_zero :
    Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 (0 : ℝ)) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

private theorem cast_hitA_u (T : ℕ) :
    (model.pathLaw (Measure.dirac u)).real (hitA T) =
      (1/3 : ℝ) * (1 - (1/2 : ℝ)^T) := by
  convert canonical_hitA_u T using 1 <;> norm_num

private theorem cast_hitB_u (T : ℕ) :
    (model.pathLaw (Measure.dirac u)).real (hitB T) =
      (2/3 : ℝ) * (1 - (1/2 : ℝ)^T) := by
  convert canonical_hitB_u T using 1 <;> norm_num

/-- Exact infinite-horizon hitting probability of absorbing state a under
the actual canonical trajectory law started at u. -/
theorem ever_hit_a_u :
    model.pathLaw (Measure.dirac u) (⋃ T : ℕ, hitA T) =
      ENNReal.ofReal (1/3 : ℝ) := by
  let P := model.pathLaw (Measure.dirac u)
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
        ENNReal.ofReal (P.real (hitA T)) = P (hitA T) := by
      exact ENNReal.ofReal_toReal (measure_ne_top P (hitA T))
    simpa only [hcon] using h
  have hcont : Tendsto (fun T : ℕ => P (hitA T))
      atTop (𝓝 (P (⋃ T : ℕ, hitA T))) :=
    tendsto_measure_iUnion_atTop (μ := P) hitA_monotone
  exact tendsto_nhds_unique hcont hE

/-- Exact infinite-horizon hitting probability of absorbing state b. -/
theorem ever_hit_b_u :
    model.pathLaw (Measure.dirac u) (⋃ T : ℕ, hitB T) =
      ENNReal.ofReal (2/3 : ℝ) := by
  let P := model.pathLaw (Measure.dirac u)
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
        ENNReal.ofReal (P.real (hitB T)) = P (hitB T) := by
      exact ENNReal.ofReal_toReal (measure_ne_top P (hitB T))
    simpa only [hcon] using h
  have hcont : Tendsto (fun T : ℕ => P (hitB T))
      atTop (𝓝 (P (⋃ T : ℕ, hitB T))) :=
    tendsto_measure_iUnion_atTop (μ := P) hitB_monotone
  exact tendsto_nhds_unique hcont hE


/-- Shifting the inclusive finite horizon by one does not change the
infinite union of endpoint visits. -/
theorem shifted_hitA_union :
    (⋃ T : ℕ, hitA (T+1)) = (⋃ T : ℕ, hitA T) := by
  ext w
  constructor
  · intro h
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨T+1, hT⟩
  · intro h
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨T, hitA_monotone (Nat.le_succ T) hT⟩

theorem shifted_hitB_union :
    (⋃ T : ℕ, hitB (T+1)) = (⋃ T : ℕ, hitB T) := by
  ext w
  constructor
  · intro h
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨T+1, hT⟩
  · intro h
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨T, hitB_monotone (Nat.le_succ T) hT⟩

private theorem cast_hitA_t (T : ℕ) :
    (model.pathLaw (Measure.dirac t)).real (hitA (T+1)) =
      (1/3 : ℝ) * (1 - (1/2 : ℝ)^T) := by
  convert canonical_hitA_t T using 1 <;> norm_num

private theorem cast_hitB_t (T : ℕ) :
    (model.pathLaw (Measure.dirac t)).real (hitB (T+1)) =
      (2/3 : ℝ) * (1 - (1/2 : ℝ)^T) := by
  convert canonical_hitB_t T using 1 <;> norm_num

/-- The deterministic entry step from t preserves the exact 1/3 endpoint
probability. This is a theorem about the genuine infinite path law. -/
theorem ever_hit_a_t :
    model.pathLaw (Measure.dirac t) (⋃ T : ℕ, hitA T) =
      ENNReal.ofReal (1/3 : ℝ) := by
  let P := model.pathLaw (Measure.dirac t)
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
        ENNReal.ofReal (P.real (hitA (T+1))) = P (hitA (T+1)) := by
      exact ENNReal.ofReal_toReal (measure_ne_top P (hitA (T+1)))
    simpa only [hcon] using h
  have hm : Monotone (fun T : ℕ => hitA (T+1)) := by
    intro m n hmn
    exact hitA_monotone (Nat.succ_le_succ hmn)
  have hcont : Tendsto (fun T : ℕ => P (hitA (T+1)))
      atTop (𝓝 (P (⋃ T : ℕ, hitA (T+1)))) :=
    tendsto_measure_iUnion_atTop (μ := P) hm
  rw [shifted_hitA_union] at hcont
  exact tendsto_nhds_unique hcont hE

theorem ever_hit_b_t :
    model.pathLaw (Measure.dirac t) (⋃ T : ℕ, hitB T) =
      ENNReal.ofReal (2/3 : ℝ) := by
  let P := model.pathLaw (Measure.dirac t)
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
        ENNReal.ofReal (P.real (hitB (T+1))) = P (hitB (T+1)) := by
      exact ENNReal.ofReal_toReal (measure_ne_top P (hitB (T+1)))
    simpa only [hcon] using h
  have hm : Monotone (fun T : ℕ => hitB (T+1)) := by
    intro m n hmn
    exact hitB_monotone (Nat.succ_le_succ hmn)
  have hcont : Tendsto (fun T : ℕ => P (hitB (T+1)))
      atTop (𝓝 (P (⋃ T : ℕ, hitB (T+1)))) :=
    tendsto_measure_iUnion_atTop (μ := P) hm
  rw [shifted_hitB_union] at hcont
  exact tendsto_nhds_unique hcont hE

end TypedEndpointInfiniteWeights
end MultipleLimit
end PermanssonResearch
