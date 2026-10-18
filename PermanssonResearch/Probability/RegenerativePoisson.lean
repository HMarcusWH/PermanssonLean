import PermanssonResearch.Probability.RegenerativeMeasure
import Mathlib.Probability.Kernel.Invariance

/-! Actual invariance and the bounded Poisson equation for a supplied
regenerative decomposition of the original Markov kernel. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace PermanssonResearch.Probability.Regenerative
set_option autoImplicit false
variable {Y : Type*} [MeasurableSpace Y] (R : Kernel Y Y) [IsMarkovKernel R]

def IsMixture (K : Kernel Y Y) (ξ : ProbabilityMeasure Y) (r : ℝ) : Prop :=
  ∀ y, K y = ENNReal.ofReal (1-r) • ξ.toMeasure + ENNReal.ofReal r • R y

theorem applyTest_mixture (K : Kernel Y Y) (ξ : ProbabilityMeasure Y) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hmix : IsMixture R K ξ r)
    {f : Y → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M) (y : Y) :
    applyTest K f y = (1-r)*(∫ z, f z ∂ξ.toMeasure) + r*applyTest R f y := by
  unfold applyTest
  rw [hmix y,integral_add_measure
    ((bounded_integrable hf hb ξ.toMeasure).smul_measure (by simp))
    ((bounded_integrable hf hb (R y)).smul_measure (by simp))]
  simp only [integral_smul_measure,ENNReal.toReal_ofReal (sub_nonneg.mpr hr1.le),
    ENNReal.toReal_ofReal hr,smul_eq_mul]

theorem resolvent_applyTest {f : Y → ℝ} (hf : Measurable f) {M r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hb : ∀ y, |f y| ≤ M) :
    resolvent R r (applyTest R f) = applyTest R (resolvent R r f) := by
  funext y
  rw [resolvent_shift,applyTest_resolvent R hf hr hr1 hb]

theorem poisson_equation (K : Kernel Y Y) (ξ : ProbabilityMeasure Y) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hmix : IsMixture R K ξ r)
    {f : Y → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M) (y : Y) :
    resolvent R r f y - applyTest K (resolvent R r f) y =
      f y - ∫ z, f z ∂law R ξ r := by
  rw [applyTest_mixture R K ξ hr hr1 hmix (resolvent_measurable R hf r)
    (resolvent_abs_bound R hr hr1 hb)]
  have he := resolvent_equation R hf hr hr1 hb y
  have hi := integral_law R ξ hr hr1 hf hb
  linarith

theorem integral_law_applyTest (ξ : ProbabilityMeasure Y) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) {f : Y → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ y, |f y| ≤ M) :
    (∫ y, applyTest R f y ∂law R ξ r) =
      (1-r) * ∫ y, applyTest R (resolvent R r f) y ∂ξ.toMeasure := by
  rw [integral_law R ξ hr hr1 (applyTest_measurable R hf) (applyTest_abs_bound R hb),
    resolvent_applyTest R hf hr hr1 hb]

theorem integral_comp_law (K : Kernel Y Y) [IsMarkovKernel K]
    (ξ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) {f : Y → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ y, |f y| ≤ M) :
    (∫ y, f y ∂(K ∘ₘ law R ξ r)) = ∫ y, f y ∂law R ξ r := by
  haveI : IsProbabilityMeasure (law R ξ r) := law_probability R ξ hr hr1
  have hg : Integrable (resolvent R r f) ξ.toMeasure :=
    bounded_integrable (resolvent_measurable R hf r) (resolvent_abs_bound R hr hr1 hb) _
  have hRg : Integrable (applyTest R (resolvent R r f)) ξ.toMeasure :=
    bounded_integrable (applyTest_measurable R (resolvent_measurable R hf r))
      (applyTest_abs_bound R (resolvent_abs_bound R hr hr1 hb)) _
  have hξ : (∫ y, resolvent R r f y ∂ξ.toMeasure) =
      (∫ y, f y ∂ξ.toMeasure) + r*(∫ y, applyTest R (resolvent R r f) y ∂ξ.toMeasure) := by
    calc
      _ = ∫ y, f y + r*applyTest R (resolvent R r f) y ∂ξ.toMeasure :=
        integral_congr_ae (ae_of_all _ (resolvent_equation R hf hr hr1 hb))
      _ = _ := by rw [integral_add (bounded_integrable hf hb _) (hRg.const_mul r),integral_const_mul]
  have hcomp : (∫ y, f y ∂(K ∘ₘ law R ξ r)) =
      (1-r)*(∫ y, f y ∂ξ.toMeasure) + r*(∫ y, applyTest R f y ∂law R ξ r) := by
    calc
      _ = ∫ y, applyTest K f y ∂law R ξ r := by
        rw [Measure.comp_eq_comp_const_apply,Kernel.integral_comp (bounded_integrable hf hb _)]
        rfl
      _ = _ := by
        simp_rw [applyTest_mixture R K ξ hr hr1 hmix hf hb]
        rw [integral_add (integrable_const _) ((bounded_integrable (applyTest_measurable R hf)
          (applyTest_abs_bound R hb) _).const_mul r),integral_const_mul]
        simp [integral_const_mul]
  rw [hcomp,integral_law_applyTest R ξ hr hr1 hf hb,integral_law R ξ hr hr1 hf hb,hξ]
  ring

theorem law_invariant (K : Kernel Y Y) [IsMarkovKernel K] (ξ : ProbabilityMeasure Y)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hmix : IsMixture R K ξ r) :
    Kernel.Invariant K (law R ξ r) := by
  haveI : IsProbabilityMeasure (law R ξ r) := law_probability R ξ hr hr1
  change K ∘ₘ law R ξ r = law R ξ r
  apply Measure.ext
  intro s hs
  let f : Y → ℝ := s.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hb : ∀ y, |f y| ≤ 1 := by
    intro y
    by_cases hy : y ∈ s <;> simp [f,Set.indicator,hy]
  have h := integral_comp_law R K ξ hr hr1 hmix hf hb
  change (∫ y, s.indicator (fun _ => (1 : ℝ)) y ∂(K ∘ₘ law R ξ r)) =
    ∫ y, s.indicator (fun _ => (1 : ℝ)) y ∂law R ξ r at h
  rw [integral_indicator_const 1 hs,integral_indicator_const 1 hs] at h
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
  simpa only [Measure.real,smul_eq_mul,mul_one] using h

end PermanssonResearch.Probability.Regenerative
