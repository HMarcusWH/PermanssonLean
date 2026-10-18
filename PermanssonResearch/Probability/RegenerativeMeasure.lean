import PermanssonResearch.Probability.RegenerativeOperator
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! The actual normalized geometric mixture of the original residual-kernel
iterates, and its integral representation by the bounded resolvent. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace PermanssonResearch.Probability.Regenerative
set_option autoImplicit false
variable {Y : Type*} [MeasurableSpace Y] (R : Kernel Y Y) [IsMarkovKernel R]

noncomputable def orbitLaw (ξ : ProbabilityMeasure Y) : ℕ → Measure Y
  | 0 => ξ.toMeasure
  | n+1 => R ∘ₘ orbitLaw ξ n

instance orbitLaw_probability (ξ : ProbabilityMeasure Y) (n : ℕ) :
    IsProbabilityMeasure (orbitLaw R ξ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure ξ.toMeasure)
  | succ n ih =>
    letI := ih
    change IsProbabilityMeasure (R ∘ₘ orbitLaw R ξ n)
    infer_instance

theorem integral_orbitLaw (ξ : ProbabilityMeasure Y) {f : Y → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ y, |f y| ≤ M) (n : ℕ) :
    (∫ y, f y ∂orbitLaw R ξ n) = ∫ y, iterateTest R f n y ∂ξ.toMeasure := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    calc
      _ = ∫ y, applyTest R f y ∂orbitLaw R ξ n := by
        change (∫ y, f y ∂(R ∘ₘ orbitLaw R ξ n)) = _
        rw [Measure.comp_eq_comp_const_apply,
          Kernel.integral_comp (bounded_integrable hf hb _)]
        rfl
      _ = ∫ y, iterateTest R (applyTest R f) n y ∂ξ.toMeasure :=
        ih (applyTest_measurable R hf) (applyTest_abs_bound R hb)
      _ = _ := by rw [iterateTest_shift]

theorem geometric_weight_sum {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, ENNReal.ofReal ((1-r)*r^n)) = 1 := by
  have hs := (summable_geometric_of_lt_one hr hr1).mul_left (1-r)
  have hsum : (∑' n : ℕ, (1-r)*r^n) = 1 := by
    rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr])]
    exact mul_inv_cancel₀ (sub_pos.mpr hr1).ne'
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (sub_nonneg.mpr hr1.le) (pow_nonneg hr n)) hs,hsum]
  simp

noncomputable def law (ξ : ProbabilityMeasure Y) (r : ℝ) : Measure Y :=
  Measure.sum (fun n => ENNReal.ofReal ((1-r)*r^n) • orbitLaw R ξ n)

theorem law_probability (ξ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    IsProbabilityMeasure (law R ξ r) := by
  apply isProbabilityMeasure_iff.mpr
  rw [law,Measure.sum_apply _ MeasurableSet.univ]
  simpa only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] using geometric_weight_sum hr hr1

noncomputable def probabilityLaw (ξ : ProbabilityMeasure Y) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) : ProbabilityMeasure Y :=
  ⟨law R ξ r,law_probability R ξ hr hr1⟩

theorem integral_law (ξ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {f : Y → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M) :
    (∫ y, f y ∂law R ξ r) = (1-r) * ∫ y, resolvent R r f y ∂ξ.toMeasure := by
  haveI : IsProbabilityMeasure (law R ξ r) := law_probability R ξ hr hr1
  have hi := bounded_integrable hf hb (law R ξ r)
  change Integrable f (Measure.sum (fun n =>
    ENNReal.ofReal ((1-r)*r^n) • orbitLaw R ξ n)) at hi
  rw [law,integral_sum_measure hi,integral_resolvent R ξ.toMeasure hf hr hr1 hb]
  simp_rw [integral_smul_measure,ENNReal.toReal_ofReal
    (mul_nonneg (sub_nonneg.mpr hr1.le) (pow_nonneg hr _)),smul_eq_mul,
    integral_orbitLaw R ξ hf hb]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

end PermanssonResearch.Probability.Regenerative
