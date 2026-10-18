import PermanssonResearch.Probability.KantorovichDual
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Tactic

/-! The original bounded one-Lipschitz test class separates Borel probability
laws on a metric space. No first-moment premise is required for separation. -/

open MeasureTheory Filter
open scoped Topology NNReal
namespace PermanssonResearch.Probability
set_option autoImplicit false
variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem integral_eq_of_dual_zero_lipschitz (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hzero : W1DualLE μ ν 0) (f : Y → ℝ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hbound : ∃ C, ∀ y, |f y| ≤ C) :
    (∫ y, f y ∂μ) = ∫ y, f y ∂ν := by
  let a : ℝ := L+1
  have ha : 0 < a := by dsimp [a]; positivity
  let g : Y → ℝ := fun y => a⁻¹*f y
  have hg : IsKRTest g := by
    refine ⟨measurable_const.mul hf.continuous.measurable,?_,?_⟩
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (a⁻¹*f x) (a⁻¹*f y) ≤ _
      rw [Real.dist_eq,← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr ha)]
      have h : |f x-f y| ≤ L*dist x y := by
        simpa [Real.dist_eq] using hf.dist_le_mul x y
      have hL : (L : ℝ) ≤ a := by dsimp [a]; linarith
      calc
        a⁻¹*|f x-f y| ≤ a⁻¹*(a*dist x y) :=
          mul_le_mul_of_nonneg_left
            (h.trans (mul_le_mul_of_nonneg_right hL dist_nonneg)) (inv_nonneg.mpr ha.le)
        _ = ((1 : ℝ≥0) : ℝ)*dist x y := by rw [inv_mul_cancel_left₀ ha.ne']; simp
    · obtain ⟨C,hC⟩ := hbound
      refine ⟨a⁻¹*C,fun y => ?_⟩
      change |a⁻¹*f y| ≤ _
      rw [abs_mul,abs_of_pos (inv_pos.mpr ha)]
      exact mul_le_mul_of_nonneg_left (hC y) (inv_nonneg.mpr ha.le)
  have h := sub_eq_zero.mp (abs_nonpos_iff.mp (hzero g hg))
  change (∫ y, a⁻¹*f y ∂μ) = (∫ y, a⁻¹*f y ∂ν) at h
  rw [integral_const_mul,integral_const_mul] at h
  exact (mul_left_cancel₀ (inv_ne_zero ha.ne')) h

theorem measure_eq_of_w1DualLE_zero (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hzero : W1DualLE μ ν 0) : μ = ν := by
  obtain ⟨y₀,_⟩ := nonempty_of_measure_ne_zero (μ := μ) (s := Set.univ) (by simp)
  let p : ProbabilityMeasure Y := ⟨μ,inferInstance⟩
  let q : ProbabilityMeasure Y := ⟨ν,inferInstance⟩
  have hweak : Tendsto (fun _ : ℕ => p) atTop (𝓝 q) := by
    apply tendsto_iff_forall_lipschitz_integral_tendsto.2
    intro f hbound hlip
    obtain ⟨C,hC⟩ := hbound
    obtain ⟨L,hL⟩ := hlip
    have habs : ∃ B, ∀ y, |f y| ≤ B := by
      refine ⟨C+|f y₀|,fun y => ?_⟩
      have hh : |f y-f y₀| ≤ C := by simpa [Real.dist_eq] using hC y y₀
      calc
        |f y| = |(f y-f y₀)+f y₀| := by congr 1; ring
        _ ≤ |f y-f y₀|+|f y₀| := abs_add_le _ _
        _ ≤ C+|f y₀| := add_le_add hh le_rfl
    have he := integral_eq_of_dual_zero_lipschitz μ ν hzero f hL habs
    change Tendsto (fun _ : ℕ => ∫ y, f y ∂μ) atTop (𝓝 (∫ y, f y ∂ν))
    rw [he]
    exact tendsto_const_nhds
  have he : p = q := tendsto_nhds_unique tendsto_const_nhds hweak
  exact congrArg ProbabilityMeasure.toMeasure he

end PermanssonResearch.Probability
