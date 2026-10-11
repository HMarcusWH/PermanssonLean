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
    have h := (tendsto_const_nhds.sub half_to_zero).const_mul (1/3 : ℝ)
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
  have hcont := tendsto_measure_iUnion_atTop (μ := P) hitA_monotone
  exact hcont.unique hE

/-- Exact infinite-horizon hitting probability of absorbing state b. -/
theorem ever_hit_b_u :
    model.pathLaw (Measure.dirac u) (⋃ T : ℕ, hitB T) =
      ENNReal.ofReal (2/3 : ℝ) := by
  let P := model.pathLaw (Measure.dirac u)
  have hR : Tendsto (fun T : ℕ => P.real (hitB T))
      atTop (𝓝 (2/3 : ℝ)) := by
    have h := (tendsto_const_nhds.sub half_to_zero).const_mul (2/3 : ℝ)
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
  have hcont := tendsto_measure_iUnion_atTop (μ := P) hitB_monotone
  exact hcont.unique hE

end TypedEndpointInfiniteWeights
end MultipleLimit
end PermanssonResearch
