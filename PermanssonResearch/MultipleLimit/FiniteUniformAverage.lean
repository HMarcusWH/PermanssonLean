import PermanssonLean.Regime.Occupation
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.UniformOn
import Mathlib.Tactic

/-!
# Generic positive-horizon finite uniform probability arithmetic

The frozen RegimeSpecification uses uniformFinProbability on Fin T for T>0.
These statements concern that very same measure. They do not import or
depend on the PeriodicExactGR example and do not alter the frozen core.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteUniformAverage

/-- The original uniform finite-horizon measure is normalized counting
measure on Fin T, for any positive T. -/
theorem uniformFinProbability_toMeasure
    (T : ℕ) (hT : 0 < T) :
    (PermanssonLean.RegimeSpecification.uniformFinProbability T hT).toMeasure =
      ((T : ℝ≥0∞)⁻¹) • Measure.count := by
  ext E hE
  change ProbabilityTheory.uniformOn (Set.univ : Set (Fin T)) E =
    (((T : ℝ≥0∞)⁻¹) • Measure.count) E
  rw [ProbabilityTheory.uniformOn_univ, Measure.smul_apply]
  simp [ENNReal.div_eq_inv_mul, mul_comm]

/-- An ordinary real-valued function on a positive finite horizon has
its exact finite arithmetic mean under the frozen uniform measure. -/
theorem integral_uniformFin_eq_average
    (T : ℕ) (hT : 0 < T) (f : Fin T → ℝ) :
    (∫ i, f i
      ∂(PermanssonLean.RegimeSpecification.uniformFinProbability T hT).toMeasure) =
      ((T : ℝ)⁻¹) * ∑ i : Fin T, f i := by
  rw [uniformFinProbability_toMeasure T hT]
  rw [integral_smul_measure, integral_count]
  simp [ENNReal.toReal_inv, smul_eq_mul]

end FiniteUniformAverage
end MultipleLimit
end PermanssonResearch
