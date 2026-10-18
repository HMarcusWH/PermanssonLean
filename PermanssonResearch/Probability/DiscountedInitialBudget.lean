import PermanssonResearch.Probability.SummablePathScores

/-! The normalized discounted whole-path score bound retains the initial
law mismatch, including the time-zero score. -/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch.Probability

theorem discounted_geometric_budget_initial {β η ε : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (∑' n : ℕ, (1-β)*β^n*(1-(1-ε)*(1-η)^n)) =
      1-(1-ε)*(1-β)/(1-β*(1-η)) := by
  have hr0 : 0 ≤ β*(1-η) := mul_nonneg hβ0 (sub_nonneg.mpr hη1)
  have hr1 : β*(1-η) < 1 :=
    (mul_le_of_le_one_right hβ0 (by linarith : 1-η ≤ 1)).trans_lt hβ1
  have hs := (summable_geometric_of_lt_one hβ0 hβ1).mul_left (1-β)
  have ht := (summable_geometric_of_lt_one hr0 hr1).mul_left ((1-ε)*(1-β))
  have heq (n : ℕ) : (1-β)*β^n*(1-(1-ε)*(1-η)^n) =
      (1-β)*β^n - ((1-ε)*(1-β))*(β*(1-η))^n := by
    rw [mul_pow]
    ring
  simp_rw [heq]
  rw [hs.tsum_sub ht, tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one hβ0 hβ1, tsum_geometric_of_lt_one hr0 hr1]
  field_simp [ne_of_gt (sub_pos.mpr hβ1), ne_of_gt (sub_pos.mpr hr1)]
  <;> ring

theorem initial_geometric_error_bounds {η ε : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (n : ℕ) :
    0 ≤ 1-(1-ε)*(1-η)^n ∧ 1-(1-ε)*(1-η)^n ≤ 1 := by
  have hp0 : 0 ≤ (1-η)^n := pow_nonneg (sub_nonneg.mpr hη1) n
  have hp1 : (1-η)^n ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hη1) (by linarith)
  have ha : 0 ≤ 1-ε := sub_nonneg.mpr hε1
  have hh := mul_le_mul_of_nonneg_left hp1 ha
  constructor
  · nlinarith
  · exact sub_le_self _ (mul_nonneg ha hp0)

theorem discounted_output_score_error_initial
    {Ω : Type*} [MeasurableSpace Ω] {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (output : (n : ℕ) → Ω → V n) (ho : ∀ n, Measurable (output n))
    (g : (n : ℕ) → V n → ℝ) (hg : ∀ n, Measurable (g n))
    (hg0 : ∀ n v, 0 ≤ g n v) (hg1 : ∀ n v, g n v ≤ 1)
    {β η ε : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (htv : ∀ n, PermanssonLean.ProbabilitySupport.eventTotalVariation
      (μ.map (output n)) (ν.map (output n)) ≤ 1-(1-ε)*(1-η)^n) :
    |(∫ ω, summablePathScore (fun n => (1-β)*β^n)
        (fun n ω => g n (output n ω)) ω ∂μ) -
      ∫ ω, summablePathScore (fun n => (1-β)*β^n)
        (fun n ω => g n (output n ω)) ω ∂ν| ≤
      1-(1-ε)*(1-β)/(1-β*(1-η)) := by
  have hw (n : ℕ) : 0 ≤ (1-β)*β^n :=
    mul_nonneg (by linarith) (pow_nonneg hβ0 n)
  have hs := (summable_geometric_of_lt_one hβ0 hβ1).mul_left (1-β)
  have he := initial_geometric_error_bounds hη0 hη1 hε0 hε1
  have hh := summable_output_score_error μ ν output ho g hg hg0 hg1
    (fun n => (1-β)*β^n) hw hs (fun n => 1-(1-ε)*(1-η)^n)
    (fun n => (he n).1) (fun n => (he n).2) htv
  simpa only [discounted_geometric_budget_initial hβ0 hβ1 hη0 hη1] using hh

theorem zero_row_defect_retains_initial_budget {β ε : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∑' n : ℕ, (1-β)*β^n*(1-(1-ε)*(1-(0 : ℝ))^n)) = ε := by
  rw [discounted_geometric_budget_initial hβ0 hβ1 (by norm_num) (by norm_num)]
  field_simp [ne_of_gt (sub_pos.mpr hβ1)]
  <;> ring

end PermanssonResearch.Probability
