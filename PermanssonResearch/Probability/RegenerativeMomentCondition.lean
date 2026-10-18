import PermanssonResearch.Probability.RegenerativeMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! A primitive integrable regenerative reward condition. Its series is
the actual expected absolute reward before a geometric regeneration;
Tonelli proves integrability under the constructed invariant law. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace PermanssonResearch.Probability.RegenerativeMoment
open Regenerative
set_option autoImplicit false
variable {Y : Type*} [MeasurableSpace Y]

def RewardCondition (R : Kernel Y Y) [IsMarkovKernel R] (ξ : ProbabilityMeasure Y)
    (r : ℝ) (f : Y → ℝ) : Prop :=
  (∑' n : ℕ, ENNReal.ofReal (r^n)*(∫⁻ y, ‖f y‖ₑ ∂orbitLaw R ξ n)) < ∞

theorem integrable_law_of_rewardCondition (R : Kernel Y Y) [IsMarkovKernel R]
    (ξ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {f : Y → ℝ} (hf : Measurable f) (hreward : RewardCondition R ξ r f) :
    Integrable f (law R ξ r) := by
  refine ⟨hf.aestronglyMeasurable,?_⟩
  change (∫⁻ y, ‖f y‖ₑ ∂law R ξ r) < ∞
  rw [law,lintegral_sum_measure]
  simp_rw [lintegral_smul_measure,smul_eq_mul,
    ENNReal.ofReal_mul (sub_nonneg.mpr hr1.le),mul_assoc]
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hreward

theorem rewardCondition_of_integrable_law (R : Kernel Y Y) [IsMarkovKernel R]
    (ξ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {f : Y → ℝ} (hf : Integrable f (law R ξ r)) : RewardCondition R ξ r f := by
  have hfin := hf.hasFiniteIntegral
  change (∫⁻ y, ‖f y‖ₑ ∂law R ξ r) < ∞ at hfin
  rw [law,lintegral_sum_measure] at hfin
  simp_rw [lintegral_smul_measure,smul_eq_mul,
    ENNReal.ofReal_mul (sub_nonneg.mpr hr1.le),mul_assoc] at hfin
  rw [ENNReal.tsum_mul_left] at hfin
  exact ENNReal.lt_top_of_mul_ne_top_right hfin.ne
    (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hr1)))

end PermanssonResearch.Probability.RegenerativeMoment
