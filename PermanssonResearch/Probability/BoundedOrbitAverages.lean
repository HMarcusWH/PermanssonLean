import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

namespace PermanssonResearch.Probability.Hopf

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {T : Ω → Ω} {f : Ω → ℝ}

def upperAverage (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) : ℝ :=
  limsup (fun n => birkhoffAverage ℝ T f n ω) atTop

theorem average_measurable (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffAverage ℝ T f n) := by
  unfold birkhoffAverage birkhoffSum
  exact (measurable_const (a := (n : ℝ)⁻¹)).smul
    (Finset.measurable_sum _ fun k _ => hf.comp (hT.iterate k))

theorem upperAverage_measurable (hT : Measurable T) (hf : Measurable f) :
    Measurable (upperAverage T f) :=
  Measurable.limsup (fun n => average_measurable hT hf n)

theorem average_abs_bound (M : ℝ) (hM : 0 ≤ M) (hf : ∀ ω, |f ω| ≤ M)
    (n : ℕ) (ω : Ω) : |birkhoffAverage ℝ T f n ω| ≤ M := by
  by_cases hn : n = 0
  · subst n
    simpa using hM
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hs : |birkhoffSum T f n ω| ≤ (n : ℝ)*M := by
    unfold birkhoffSum
    calc
      _ ≤ ∑ k ∈ Finset.range n, |f (T^[k] ω)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range n, M := Finset.sum_le_sum (fun k _ => hf _)
      _ = (n : ℝ)*M := by simp
  calc
    |birkhoffAverage ℝ T f n ω| = (n : ℝ)⁻¹ * |birkhoffSum T f n ω| := by
      simp [birkhoffAverage, abs_mul]
    _ ≤ (n : ℝ)⁻¹ * ((n : ℝ)*M) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ = M := by rw [← mul_assoc, inv_mul_cancel₀ hnR, one_mul]

theorem average_bddAbove (M : ℝ) (hM : 0 ≤ M) (hf : ∀ ω, |f ω| ≤ M) (ω : Ω) :
    IsBoundedUnder (· ≤ ·) atTop (fun n => birkhoffAverage ℝ T f n ω) :=
  isBoundedUnder_of ⟨M, fun n => (abs_le.mp (average_abs_bound M hM hf n ω)).2⟩

theorem average_bddBelow (M : ℝ) (hM : 0 ≤ M) (hf : ∀ ω, |f ω| ≤ M) (ω : Ω) :
    IsBoundedUnder (· ≥ ·) atTop (fun n => birkhoffAverage ℝ T f n ω) :=
  isBoundedUnder_of ⟨-M, fun n => (abs_le.mp (average_abs_bound M hM hf n ω)).1⟩

theorem upperAverage_abs_bound (M : ℝ) (hM : 0 ≤ M) (hf : ∀ ω, |f ω| ≤ M)
    (ω : Ω) : |upperAverage T f ω| ≤ M := by
  have hu := average_bddAbove (T := T) M hM hf ω
  have hl := average_bddBelow (T := T) M hM hf ω
  apply abs_le.mpr
  constructor
  · exact (le_liminf_of_le hu.isCoboundedUnder_ge
      (Eventually.of_forall fun n => (abs_le.mp (average_abs_bound M hM hf n ω)).1)).trans
      (liminf_le_limsup hu hl)
  · exact limsup_le_of_le hl.isCoboundedUnder_le
      (Eventually.of_forall fun n => (abs_le.mp (average_abs_bound M hM hf n ω)).2)

theorem limsup_le_of_tendsto_sub {u v : ℕ → ℝ} (M : ℝ)
    (hu : ∀ n, |u n| ≤ M) (hv : ∀ n, |v n| ≤ M)
    (hd : Tendsto (fun n => u n-v n) atTop (𝓝 0)) :
    limsup u atTop ≤ limsup v atTop := by
  have huL : IsBoundedUnder (· ≥ ·) atTop u :=
    isBoundedUnder_of ⟨-M, fun n => (abs_le.mp (hu n)).1⟩
  have hvU : IsBoundedUnder (· ≤ ·) atTop v :=
    isBoundedUnder_of ⟨M, fun n => (abs_le.mp (hv n)).2⟩
  have hvL : IsBoundedUnder (· ≥ ·) atTop v :=
    isBoundedUnder_of ⟨-M, fun n => (abs_le.mp (hv n)).1⟩
  have he : ∀ ε > 0, limsup u atTop ≤ limsup v atTop + ε := by
    intro ε hε
    have hs := (tendsto_order.mp hd).2 ε hε
    have hh : ∀ᶠ n in atTop, u n ≤ v n + ε := hs.mono fun n hn => by linarith
    have hvε : IsBoundedUnder (· ≤ ·) atTop (fun n => v n + ε) :=
      isBoundedUnder_of ⟨M+ε, fun n => add_le_add (abs_le.mp (hv n)).2 le_rfl⟩
    have hle := limsup_le_limsup hh huL.isCoboundedUnder_le hvε
    rwa [limsup_add_const atTop v ε hvU hvL.isCoboundedUnder_le] at hle
  by_contra h
  have hp : 0 < (limsup u atTop-limsup v atTop)/2 := by linarith
  have hh := he _ hp
  linarith

theorem upperAverage_invariant (M : ℝ) (hM : 0 ≤ M) (hf : ∀ ω, |f ω| ≤ M)
    (ω : Ω) : upperAverage T f (T ω) = upperAverage T f ω := by
  have hb : Bornology.IsBounded (Set.range f) := Metric.isBounded_range_iff.mpr
    ⟨2*M, fun x y => by
      calc
        dist (f x) (f y) ≤ dist (f x) 0 + dist 0 (f y) := dist_triangle _ _ _
        _ ≤ 2*M := by
          simp only [Real.dist_eq, sub_zero, zero_sub, abs_neg]
          linarith [hf x, hf y]⟩
  have hd := tendsto_birkhoffAverage_apply_sub_birkhoffAverage' (𝕜 := ℝ) hb T ω
  apply le_antisymm
  · exact limsup_le_of_tendsto_sub M
      (fun n => average_abs_bound M hM hf n (T ω))
      (fun n => average_abs_bound M hM hf n ω) hd
  · have hd' := hd.neg
    simp only [neg_sub, neg_zero] at hd'
    exact limsup_le_of_tendsto_sub M
      (fun n => average_abs_bound M hM hf n ω)
      (fun n => average_abs_bound M hM hf n (T ω)) hd'

end
end PermanssonResearch.Probability.Hopf
