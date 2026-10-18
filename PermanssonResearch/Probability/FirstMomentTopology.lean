import PermanssonResearch.Probability.FirstMomentEmpirical
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! The genuine transport topology maps continuously to the original weak
probability topology. Bounded Lipschitz test integrals give the bridge. -/

open MeasureTheory Filter TopologicalSpace
open scoped Topology NNReal

namespace PermanssonResearch.Probability.FirstMomentProbability

set_option autoImplicit false
variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V] [SeparableSpace V]
variable {v₀ : V}

theorem bounded_integral_lipschitz (f : V → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (hbound : ∃ C, ∀ v, |f v| ≤ C) :
    LipschitzWith (L+1) (fun μ : FirstMomentProbability v₀ => ∫ v, f v ∂μ.measure) := by
  let a : ℝ := L+1
  have ha : 0 < a := by dsimp [a]; positivity
  let g : V → ℝ := fun v => a⁻¹*f v
  have hg : IsKRTest g := by
    refine ⟨measurable_const.mul hf.continuous.measurable, ?_, ?_⟩
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (a⁻¹*f x) (a⁻¹*f y) ≤ _
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr ha)]
      have h : |f x-f y| ≤ L*dist x y := by simpa [Real.dist_eq] using hf.dist_le_mul x y
      have hL : (L : ℝ) ≤ a := by dsimp [a]; linarith
      calc
        a⁻¹*|f x-f y| ≤ a⁻¹*(a*dist x y) :=
          mul_le_mul_of_nonneg_left
            (h.trans (mul_le_mul_of_nonneg_right hL dist_nonneg)) (inv_nonneg.mpr ha.le)
        _ = ((1 : ℝ≥0) : ℝ)*dist x y := by rw [inv_mul_cancel_left₀ ha.ne']; simp
    · obtain ⟨C,hC⟩ := hbound
      refine ⟨a⁻¹*C,fun v => ?_⟩
      change |a⁻¹*f v| ≤ _
      rw [abs_mul,abs_of_pos (inv_pos.mpr ha)]
      exact mul_le_mul_of_nonneg_left (hC v) (inv_nonneg.mpr ha.le)
  apply LipschitzWith.of_dist_le_mul
  intro μ ν
  have h := dual_distance μ ν g hg
  change |(∫ v, a⁻¹*f v ∂μ.measure) - ∫ v, a⁻¹*f v ∂ν.measure| ≤ dist μ ν at h
  rw [integral_const_mul, integral_const_mul, ← mul_sub, abs_mul,
    abs_of_pos (inv_pos.mpr ha)] at h
  have hh := mul_le_mul_of_nonneg_left h ha.le
  rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at hh
  simpa only [Real.dist_eq, NNReal.coe_add, NNReal.coe_one, a] using hh

theorem probability_continuous :
    Continuous (fun μ : FirstMomentProbability v₀ => μ.probability) := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hbound hlip
  obtain ⟨C,hC⟩ := hbound
  obtain ⟨L,hL⟩ := hlip
  have hb : ∃ B, ∀ v, |f v| ≤ B := by
    refine ⟨C+|f v₀|,fun v => ?_⟩
    have hh : |f v-f v₀| ≤ C := by simpa [Real.dist_eq] using hC v v₀
    have ht := abs_sub_le (f v) (f v₀) 0
    simp only [sub_zero] at ht
    linarith
  exact (bounded_integral_lipschitz f hL hb).continuous.continuousAt

end PermanssonResearch.Probability.FirstMomentProbability
