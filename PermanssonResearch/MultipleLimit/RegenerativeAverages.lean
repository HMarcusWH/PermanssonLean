import PermanssonResearch.Probability.RegenerativePoisson
import PermanssonResearch.MultipleLimit.CanonicalBoundedInnovations

/-! All-initial actual canonical time averages for a regenerative kernel,
derived from the constructed bounded Poisson solution and innovations. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace PermanssonResearch.MultipleLimit.Regenerative
open PermanssonResearch.Probability.Regenerative CanonicalBoundedInnovations FiniteCanonicalPath
set_option autoImplicit false
variable {Y : Type*} [MeasurableSpace Y]

theorem sum_poisson_identity (K : Kernel Y Y) (f g : Y → ℝ) (c : ℝ)
    (he : ∀ y, g y-predict K g y = f y-c) (w : ℕ → Y) (N : ℕ) :
    (∑ t ∈ Finset.range N, f (w t)) - (N : ℝ)*c =
      (∑ t ∈ Finset.range N, innovation K g t w) - (g (w N)-g (w 0)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one,innovation]
    simp only [innovation] at ih
    have h := he (w n)
    linarith

theorem endpoint_average_tendsto_zero (g : Y → ℝ) {B : ℝ}
    (hb : ∀ y, |g y| ≤ B) (w : ℕ → Y) :
    Tendsto (fun n => (g (w (n+1))-g (w 0))/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hu : Tendsto (fun n : ℕ => (2*B)/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (2*B))
  have hbound (n : ℕ) : |(g (w (n+1))-g (w 0))/((n+1 : ℕ) : ℝ)| ≤
      (2*B)/((n+1 : ℕ) : ℝ) := by
    rw [abs_div,abs_of_pos (show (0 : ℝ) < ((n+1 : ℕ) : ℝ) by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (abs_sub _ _).trans ((add_le_add (hb _) (hb _)).trans_eq (by ring))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero (fun _ => abs_nonneg _) hbound hu

variable [StandardBorelSpace Y] [Nonempty Y]

theorem averages_of_bounded_poisson (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : ProbabilityMeasure Y) (f g : Y → ℝ) (hg : Measurable g) (c B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ y, |g y| ≤ B)
    (he : ∀ y, g y-predict K g y = f y-c) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => (∑ t ∈ Finset.range (n+1), f (w t))/((n+1 : ℕ) : ℝ))
        atTop (𝓝 c) := by
  filter_upwards [canonical_innovation_strong_law K μ g hg B hB hb] with w hw
  have ht := (tendsto_const_nhds (x := c)).add
    (hw.sub (endpoint_average_tendsto_zero g hb w))
  have hid (n : ℕ) : (∑ t ∈ Finset.range (n+1), f (w t))/((n+1 : ℕ) : ℝ) =
      c + (∑ t ∈ Finset.range (n+1), innovation K g t w)/((n+1 : ℕ) : ℝ) -
        (g (w (n+1))-g (w 0))/((n+1 : ℕ) : ℝ) := by
    have h := sum_poisson_identity K f g c he w (n+1)
    have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    linarith
  simp only [sub_zero,add_zero] at ht
  exact ht.congr (fun n => by rw [hid]; ring)

theorem canonical_regenerative_averages (K R : Kernel Y Y) [IsMarkovKernel K]
    [IsMarkovKernel R] (ξ μ : ProbabilityMeasure Y) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hmix : IsMixture R K ξ r)
    {f : Y → ℝ} (hf : Measurable f) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ y, |f y| ≤ M) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => (∑ t ∈ Finset.range (n+1), f (w t))/((n+1 : ℕ) : ℝ))
        atTop (𝓝 (∫ y, f y ∂law R ξ r)) := by
  apply averages_of_bounded_poisson K μ f (resolvent R r f)
    (resolvent_measurable R hf r) (∫ y, f y ∂law R ξ r) (M/(1-r))
    (div_nonneg hM (sub_nonneg.mpr hr1.le)) (resolvent_abs_bound R hr hr1 hb)
  exact poisson_equation R K ξ hr hr1 hmix hf hb

end PermanssonResearch.MultipleLimit.Regenerative
