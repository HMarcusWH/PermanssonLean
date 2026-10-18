import PermanssonResearch.Probability.L1Truncation
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Convergence of real Cesaro averages is a genuinely shift-invariant
measurable event, even for unbounded observables. No bounded-endpoint
estimate is used for this deterministic assertion. -/

open MeasureTheory Filter
open scoped Topology
namespace PermanssonResearch.Probability.CesaroShift
set_option autoImplicit false
variable {Ω : Type*}

noncomputable def positiveAverage (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  birkhoffAverage ℝ T f (n+1) ω

theorem positive_shift_identity (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    positiveAverage T f n (T ω) =
      (1+1/((n+1 : ℕ) : ℝ))*positiveAverage T f (n+1) ω - f ω/((n+1 : ℕ) : ℝ) := by
  unfold positiveAverage birkhoffAverage
  rw [birkhoffSum_succ_apply' T f (n+1) ω]
  simp only [smul_eq_mul,Nat.cast_add,Nat.cast_one]
  have h1 : (n : ℝ)+1 ≠ 0 := by positivity
  have h2 : (n : ℝ)+1+1 ≠ 0 := by positivity
  field_simp [h1,h2]
  <;> ring

theorem positive_unshift_identity (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    positiveAverage T f (n+1) ω =
      (1-1/((n+1+1 : ℕ) : ℝ))*positiveAverage T f n (T ω) + f ω/((n+1+1 : ℕ) : ℝ) := by
  unfold positiveAverage birkhoffAverage
  rw [birkhoffSum_succ_apply' T f (n+1) ω]
  simp only [smul_eq_mul,Nat.cast_add,Nat.cast_one]
  have h1 : (n : ℝ)+1 ≠ 0 := by positivity
  have h2 : (n : ℝ)+1+1 ≠ 0 := by positivity
  field_simp [h1,h2]
  <;> ring

theorem positive_limit_shift_iff (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) (c : ℝ) :
    Tendsto (fun n => positiveAverage T f n (T ω)) atTop (𝓝 c) ↔
      Tendsto (fun n => positiveAverage T f n ω) atTop (𝓝 c) := by
  have hd1 (a : ℝ) : Tendsto (fun n : ℕ => a/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat a)
  have hd2 (a : ℝ) : Tendsto (fun n : ℕ => a/((n+1+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat a)
  constructor
  · intro h
    apply (tendsto_add_atTop_iff_nat 1).1
    simp_rw [positive_unshift_identity]
    simpa only [sub_zero,one_mul,add_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (hd2 1)).mul h |>.add (hd2 (f ω))
  · intro h
    simp_rw [positive_shift_identity]
    simpa only [Function.comp_apply,add_zero,one_mul,sub_zero] using!
      ((tendsto_const_nhds (x := (1 : ℝ))).add (hd1 1)).mul
        (h.comp (tendsto_add_atTop_nat 1)) |>.sub (hd1 (f ω))

theorem average_limit_shift_iff (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) (c : ℝ) :
    Tendsto (fun n => birkhoffAverage ℝ T f n (T ω)) atTop (𝓝 c) ↔
      Tendsto (fun n => birkhoffAverage ℝ T f n ω) atTop (𝓝 c) := by
  constructor
  · intro h
    apply (tendsto_add_atTop_iff_nat 1).1
    exact (positive_limit_shift_iff T f ω c).1
      ((tendsto_add_atTop_iff_nat 1).2 h)
  · intro h
    apply (tendsto_add_atTop_iff_nat 1).1
    exact (positive_limit_shift_iff T f ω c).2
      ((tendsto_add_atTop_iff_nat 1).2 h)

theorem average_limit_measurable [MeasurableSpace Ω] {T : Ω → Ω} {f : Ω → ℝ}
    (hT : Measurable T) (hf : Measurable f) (c : ℝ) :
    MeasurableSet {ω | Tendsto (fun n => birkhoffAverage ℝ T f n ω) atTop (𝓝 c)} :=
  measurableSet_tendsto_fun (fun n => Hopf.average_measurable hT hf n) measurable_const

end PermanssonResearch.Probability.CesaroShift
