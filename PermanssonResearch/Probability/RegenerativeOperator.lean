import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! The actual bounded geometric resolvent of a Markov kernel. -/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.Probability.Regenerative
set_option autoImplicit false
variable {Y : Type*} [MeasurableSpace Y] (R : Kernel Y Y) [IsMarkovKernel R]

noncomputable def applyTest (f : Y → ℝ) (y : Y) : ℝ := ∫ z, f z ∂R y

noncomputable def iterateTest (f : Y → ℝ) : ℕ → Y → ℝ
  | 0 => f
  | n+1 => applyTest R (iterateTest f n)

theorem applyTest_measurable {f : Y → ℝ} (hf : Measurable f) :
    Measurable (applyTest R f) := hf.stronglyMeasurable.integral_kernel.measurable

theorem applyTest_abs_bound {f : Y → ℝ} {M : ℝ} (hb : ∀ y, |f y| ≤ M) (y : Y) :
    |applyTest R f y| ≤ M := by
  simpa only [applyTest,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (f := f) (C := M)
      (μ := R y) (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb z)

theorem iterateTest_measurable {f : Y → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (iterateTest R f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact applyTest_measurable R ih

theorem iterateTest_abs_bound {f : Y → ℝ} {M : ℝ} (hb : ∀ y, |f y| ≤ M) (n : ℕ) :
    ∀ y, |iterateTest R f n y| ≤ M := by
  induction n with
  | zero => exact hb
  | succ n ih => exact applyTest_abs_bound R ih

theorem iterateTest_shift (f : Y → ℝ) (n : ℕ) :
    iterateTest R (applyTest R f) n = iterateTest R f (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterateTest,ih]

noncomputable def resolvent (r : ℝ) (f : Y → ℝ) (y : Y) : ℝ :=
  ∑' n, r^n * iterateTest R f n y

theorem weighted_bound {f : Y → ℝ} {M r : ℝ} (hr : 0 ≤ r)
    (hb : ∀ y, |f y| ≤ M) (n : ℕ) (y : Y) :
    ‖r^n * iterateTest R f n y‖ ≤ r^n*M := by
  rw [norm_mul,Real.norm_of_nonneg (pow_nonneg hr n),Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (iterateTest_abs_bound R hb n y) (pow_nonneg hr n)

theorem weighted_summable {f : Y → ℝ} {M r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hb : ∀ y, |f y| ≤ M) (y : Y) :
    Summable (fun n => r^n * iterateTest R f n y) :=
  ((summable_geometric_of_lt_one hr hr1).mul_right M).of_norm_bounded
    (fun n => weighted_bound R hr hb n y)

theorem resolvent_measurable {f : Y → ℝ} (hf : Measurable f) (r : ℝ) :
    Measurable (resolvent R r f) :=
  Measurable.tsum (fun n => measurable_const.mul (iterateTest_measurable R hf n))

theorem resolvent_abs_bound {f : Y → ℝ} {M r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hb : ∀ y, |f y| ≤ M) (y : Y) : |resolvent R r f y| ≤ M/(1-r) := by
  have hgeom := (summable_geometric_of_lt_one hr hr1).hasSum.mul_right M
  have ht : HasSum (fun n : ℕ => r^n*M) (M/(1-r)) := by
    convert hgeom using 1
    rw [tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr])]
    simp [div_eq_mul_inv,mul_comm]
  exact (show ‖resolvent R r f y‖ ≤ M/(1-r) from
    tsum_of_norm_bounded ht (fun n => weighted_bound R hr hb n y))

theorem bounded_integrable {f : Y → ℝ} (hf : Measurable f) {M : ℝ}
    (hb : ∀ y, |f y| ≤ M) (μ : Measure Y) [IsFiniteMeasure μ] : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M
    (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hb y)

theorem integral_resolvent (μ : Measure Y) [IsProbabilityMeasure μ]
    {f : Y → ℝ} (hf : Measurable f) {M r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hb : ∀ y, |f y| ≤ M) :
    (∫ y, resolvent R r f y ∂μ) = ∑' n, r^n * ∫ y, iterateTest R f n y ∂μ := by
  have hi (n : ℕ) : Integrable (fun y => r^n*iterateTest R f n y) μ :=
    (bounded_integrable (iterateTest_measurable R hf n)
      (iterateTest_abs_bound R hb n) μ).const_mul _
  have hs : Summable (fun n => ∫ y, ‖r^n*iterateTest R f n y‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
      (fun n => ?_) ((summable_geometric_of_lt_one hr hr1).mul_right M)
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (hi n).norm (integrable_const (r^n*M))
        (fun y => weighted_bound R hr hb n y)
  have h := (integral_tsum_of_summable_integral_norm hi hs).symm
  simpa only [resolvent,integral_const_mul] using h

theorem applyTest_resolvent {f : Y → ℝ} (hf : Measurable f) {M r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hb : ∀ y, |f y| ≤ M) (y : Y) :
    applyTest R (resolvent R r f) y =
      ∑' n, r^n * iterateTest R f (n+1) y := by
  exact integral_resolvent R (R y) hf hr hr1 hb

theorem resolvent_equation {f : Y → ℝ} (hf : Measurable f) {M r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hb : ∀ y, |f y| ≤ M) (y : Y) :
    resolvent R r f y = f y + r * applyTest R (resolvent R r f) y := by
  rw [applyTest_resolvent R hf hr hr1 hb]
  have hs := weighted_summable R hr hr1 hb y
  have he := hs.tsum_eq_zero_add
  change resolvent R r f y = _ at he
  rw [he]
  simp only [pow_zero,iterateTest,one_mul]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [pow_succ]
  ring

theorem resolvent_shift {f : Y → ℝ} {r : ℝ} :
    resolvent R r (applyTest R f) = fun y => ∑' n, r^n * iterateTest R f (n+1) y := by
  funext y
  apply tsum_congr
  intro n
  rw [iterateTest_shift]

end PermanssonResearch.Probability.Regenerative
