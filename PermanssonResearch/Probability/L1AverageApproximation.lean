import PermanssonResearch.Probability.L1Maximal

/-! An integrable observable inherits an almost-sure average limit from L1
approximants. Uniform-in-time control comes from the proved Hopf inequality. -/

open MeasureTheory Filter Set
open scoped Topology

namespace PermanssonResearch.Probability.Hopf

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {T : Ω → Ω}

theorem ae_average_limit_of_L1_approximation (hT : MeasurePreserving T μ μ)
    (f : Ω → ℝ) (hf : Measurable f) (hfi : Integrable f μ)
    (g : ℕ → Ω → ℝ) (hg : ∀ k, Measurable (g k)) (hgi : ∀ k, Integrable (g k) μ)
    (c : ℕ → ℝ) (l : ℝ)
    (hL1 : Tendsto (fun k => ∫ ω, |f ω - g k ω| ∂μ) atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 l))
    (hav : ∀ k, ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverage ℝ T (g k) n ω)
      atTop (𝓝 (c k))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n ω) atTop (𝓝 l) := by
  have heps (ε : ℝ) (hε : 0 < ε) :
      ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, |birkhoffAverage ℝ T f n ω - l| ≤ ε := by
    let B : Set Ω := {ω | ¬ ∀ᶠ n in atTop, |birkhoffAverage ℝ T f n ω - l| ≤ ε}
    have hk : ∀ᶠ k in atTop, |c k - l| < ε/3 := by
      simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hc) (ε/3) (by positivity)
    have hb : ∀ᶠ k in atTop,
        (ε/3) * μ.real B ≤ ∫ ω, |f ω - g k ω| ∂μ := by
      filter_upwards [hk] with k hck
      let E := maximalEvent T (fun ω => |f ω - g k ω| - ε/3)
      have hsub : B ≤ᵐ[μ] E := by
        filter_upwards [hav k] with ω hω
        intro hB
        by_contra hnE
        have hn (n : ℕ) : birkhoffAverage ℝ T (fun ω => |f ω - g k ω|) n ω ≤ ε/3 := by
          by_contra hgt
          exact hnE (average_gt_mem_maximalEvent _ (by positivity) n ω (lt_of_not_ge hgt))
        have havg : ∀ᶠ n in atTop,
            |birkhoffAverage ℝ T (g k) n ω - c k| < ε/3 := by
          simpa only [Real.dist_eq] using
            (Metric.tendsto_nhds.mp hω) (ε/3) (by positivity)
        apply hB
        filter_upwards [havg] with n hnk
        have hdiff := (average_sub_abs_le T f (g k) n ω).trans (hn n)
        have htri := abs_sub_le (birkhoffAverage ℝ T f n ω)
          (birkhoffAverage ℝ T (g k) n ω) l
        have htri' := abs_sub_le (birkhoffAverage ℝ T (g k) n ω) (c k) l
        linarith
      have hm : μ.real B ≤ μ.real E :=
        ENNReal.toReal_mono (measure_ne_top μ E) (measure_mono_ae hsub)
      have hgm : Measurable (fun ω => |f ω - g k ω|) := by
        simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hf.sub (hg k)).norm
      exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans
        (maximalEvent_measure_bound hT hgm (hfi.sub (hgi k)).abs
          (fun _ => abs_nonneg _) (by positivity))
    have hz : (ε/3) * μ.real B ≤ 0 := ge_of_tendsto hL1 hb
    have hzero : μ.real B = 0 := by
      have := measureReal_nonneg (μ := μ) (s := B)
      nlinarith
    have hnull : μ B = 0 := (measureReal_eq_zero_iff (μ := μ) (s := B)).mp hzero
    exact (ae_iff.mpr hnull)
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ᶠ n in atTop,
      |birkhoffAverage ℝ T f n ω - l| ≤ (1 : ℝ)/(k+1) :=
    ae_all_iff.mpr (fun k => heps _ (by positivity))
  filter_upwards [hall] with ω hω
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω k] with n hn
  simpa only [Real.dist_eq] using hn.trans_lt hk

end
end PermanssonResearch.Probability.Hopf
