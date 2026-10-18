import PermanssonResearch.Probability.EventTVCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed

/-! Q-DISCOUNT: a genuine whole-path integral class. The property is fixed as
an absolutely convergent sum of bounded measurable scores. Infinite survival
indicators are outside this class unless separately represented and proved. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace PermanssonResearch.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

theorem bounded_score_integral_error
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : Ω → ℝ) (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1) :
    |(∫ ω, g ω ∂μ) - ∫ ω, g ω ∂ν| ≤
      PermanssonLean.ProbabilitySupport.eventTotalVariation μ ν := by
  have hlin := abs_lintegral_toReal_sub_le_eventTotalVariation μ ν hg.ennreal_ofReal
    (fun ω => ENNReal.ofReal_le_one.mpr (hg1 ω))
  have hc (θ : Measure Ω) :
      (∫ ω, g ω ∂θ) = (∫⁻ ω, ENNReal.ofReal (g ω) ∂θ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.aestronglyMeasurable
  rw [hc μ, hc ν]
  exact hlin

noncomputable def summablePathScore (w : ℕ → ℝ) (g : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' n, w n * g n ω

theorem weighted_score_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (g : ℕ → Ω → ℝ)
    (hg : ∀ n, Measurable (g n)) (hg0 : ∀ n ω, 0 ≤ g n ω)
    (hg1 : ∀ n ω, g n ω ≤ 1) (n : ℕ) :
    Integrable (fun ω => w n * g n ω) μ := by
  apply Integrable.mono' (integrable_const (w n))
    ((hg n).const_mul _).aestronglyMeasurable
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw n) (hg0 n ω))]
  simpa using mul_le_mul_of_nonneg_left (hg1 n ω) (hw n)

theorem integral_summablePathScore (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hws : Summable w)
    (g : ℕ → Ω → ℝ) (hg : ∀ n, Measurable (g n))
    (hg0 : ∀ n ω, 0 ≤ g n ω) (hg1 : ∀ n ω, g n ω ≤ 1) :
    (∫ ω, summablePathScore w g ω ∂μ) = ∑' n, w n * ∫ ω, g n ω ∂μ := by
  have hi := weighted_score_integrable μ w hw g hg hg0 hg1
  have hb (n) : (∫ ω, ‖w n * g n ω‖ ∂μ) ≤ w n := by
    calc
      _ ≤ ∫ _ω : Ω, w n ∂μ := by
        apply integral_mono (hi n).norm (integrable_const _)
        intro ω
        change ‖w n * g n ω‖ ≤ w n
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw n) (hg0 n ω))]
        simpa using mul_le_mul_of_nonneg_left (hg1 n ω) (hw n)
      _ = _ := by simp
  have hs : Summable (fun n => ∫ ω, ‖w n * g n ω‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) hb hws
  unfold summablePathScore
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  simp only [integral_const_mul]

/-- Pointwise score-error budgets sum under the original whole-path property. -/
theorem summablePathScore_integral_error
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hws : Summable w)
    (g : ℕ → Ω → ℝ) (hg : ∀ n, Measurable (g n))
    (hg0 : ∀ n ω, 0 ≤ g n ω) (hg1 : ∀ n ω, g n ω ≤ 1)
    (e : ℕ → ℝ) (he0 : ∀ n, 0 ≤ e n) (he1 : ∀ n, e n ≤ 1)
    (herr : ∀ n, |(∫ ω, g n ω ∂μ) - ∫ ω, g n ω ∂ν| ≤ e n) :
    |(∫ ω, summablePathScore w g ω ∂μ) - ∫ ω, summablePathScore w g ω ∂ν| ≤
      ∑' n, w n * e n := by
  have hwe : Summable (fun n => w n * e n) := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (hw n) (he0 n)) _ hws
    intro n
    simpa using mul_le_mul_of_nonneg_left (he1 n) (hw n)
  have hbound (n) : ‖w n * ((∫ ω, g n ω ∂μ) - ∫ ω, g n ω ∂ν)‖ ≤ w n * e n := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw n)]
    exact mul_le_mul_of_nonneg_left (herr n) (hw n)
  have hs := Summable.of_norm_bounded hwe hbound
  have hint (θ : Measure Ω) [IsProbabilityMeasure θ] :
      Summable (fun n => w n * ∫ ω, g n ω ∂θ) := by
    apply Summable.of_norm_bounded hws
    intro n
    have h0 : 0 ≤ ∫ ω, g n ω ∂θ := integral_nonneg (hg0 n)
    have h1 : (∫ ω, g n ω ∂θ) ≤ 1 := by
      have hgi : Integrable (g n) θ :=
        (weighted_score_integrable θ (fun _ => 1) (fun _ => zero_le_one)
          g hg hg0 hg1 n).congr (by simp)
      simpa using integral_mono hgi (integrable_const (1 : ℝ)) (hg1 n)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw n) h0)]
    simpa using mul_le_mul_of_nonneg_left h1 (hw n)
  rw [integral_summablePathScore μ w hw hws g hg hg0 hg1,
    integral_summablePathScore ν w hw hws g hg hg0 hg1,
    ← (hint μ).tsum_sub (hint ν)]
  simp_rw [← mul_sub]
  calc
    |∑' n, w n * ((∫ ω, g n ω ∂μ) - ∫ ω, g n ω ∂ν)| ≤
        ∑' n, ‖w n * ((∫ ω, g n ω ∂μ) - ∫ ω, g n ω ∂ν)‖ := by
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ _ := Summable.tsum_le_tsum hbound hs.norm hwe

/-- Closed form of the geometric-prefix budget for normalized discounting. -/
theorem discounted_geometric_budget {β η : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (∑' n : ℕ, (1 - β) * β ^ n * (1 - (1 - η) ^ n)) =
      β * η / (1 - β * (1 - η)) := by
  have hr0 : 0 ≤ β * (1 - η) := mul_nonneg hβ0 (sub_nonneg.mpr hη1)
  have hr1 : β * (1 - η) < 1 :=
    (mul_le_of_le_one_right hβ0 (by linarith : 1 - η ≤ 1)).trans_lt hβ1
  have hbs := (summable_geometric_of_lt_one hβ0 hβ1).mul_left (1 - β)
  have hrs := (summable_geometric_of_lt_one hr0 hr1).mul_left (1 - β)
  have heq (n : ℕ) : (1 - β) * β ^ n * (1 - (1 - η) ^ n) =
      (1 - β) * β ^ n - (1 - β) * (β * (1 - η)) ^ n := by
    rw [mul_pow]
    ring
  simp_rw [heq]
  rw [hbs.tsum_sub hrs, tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one hβ0 hβ1, tsum_geometric_of_lt_one hr0 hr1]
  field_simp [ne_of_gt (sub_pos.mpr hβ1), ne_of_gt (sub_pos.mpr hr1)]
  <;> ring

/-- The whole-path property is built from declared measurable finite outputs.
Its budget follows from TV of those actual output laws. -/
theorem summable_output_score_error
    {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (output : (n : ℕ) → Ω → V n) (ho : ∀ n, Measurable (output n))
    (g : (n : ℕ) → V n → ℝ) (hg : ∀ n, Measurable (g n))
    (hg0 : ∀ n v, 0 ≤ g n v) (hg1 : ∀ n v, g n v ≤ 1)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hws : Summable w)
    (e : ℕ → ℝ) (he0 : ∀ n, 0 ≤ e n) (he1 : ∀ n, e n ≤ 1)
    (htv : ∀ n, PermanssonLean.ProbabilitySupport.eventTotalVariation
      (μ.map (output n)) (ν.map (output n)) ≤ e n) :
    |(∫ ω, summablePathScore w (fun n ω => g n (output n ω)) ω ∂μ) -
      ∫ ω, summablePathScore w (fun n ω => g n (output n ω)) ω ∂ν| ≤
      ∑' n, w n * e n := by
  apply summablePathScore_integral_error μ ν w hw hws _
    (fun n => (hg n).comp (ho n)) (fun n ω => hg0 n _) (fun n ω => hg1 n _)
    e he0 he1
  intro n
  letI := (Measure.isProbabilityMeasure_map_iff (ho n).aemeasurable).mpr
    (inferInstance : IsProbabilityMeasure μ)
  letI := (Measure.isProbabilityMeasure_map_iff (ho n).aemeasurable).mpr
    (inferInstance : IsProbabilityMeasure ν)
  have h := (bounded_score_integral_error (μ.map (output n)) (ν.map (output n))
    (g n) (hg n) (hg0 n) (hg1 n)).trans (htv n)
  simpa only [integral_map (ho n).aemeasurable (hg n).aestronglyMeasurable,
    Function.comp_def] using h

end PermanssonResearch.Probability
