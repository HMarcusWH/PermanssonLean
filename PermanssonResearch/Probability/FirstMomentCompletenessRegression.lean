import PermanssonResearch.Probability.FirstMomentCompleteness
import PermanssonResearch.Probability.FirstMomentTransportRegression

/-! Infinite-ambient regressions for the constructed complete transport space. -/

open MeasureTheory Filter
open scoped Topology
namespace PermanssonResearch.Probability.FirstMomentCompletenessRegression
set_option autoImplicit false

noncomputable def realDirac (x : ℝ) : FirstMomentProbability (0 : ℝ) :=
  ⟨⟨Measure.dirac x,inferInstance⟩,integrable_dirac (by simp)⟩

theorem real_complete : CompleteSpace (FirstMomentProbability (0 : ℝ)) := inferInstance

theorem real_dirac_distance_three : dist (realDirac 0) (realDirac 3) = 3 :=
  FirstMomentTransportRegression.real_dirac_distance_three

theorem real_distinct_laws_not_zero : dist (realDirac 0) (realDirac 3) ≠ 0 := by
  rw [real_dirac_distance_three]
  norm_num

theorem realDirac_lipschitz : LipschitzWith 1 realDirac := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  apply FirstMomentProbability.distance_le
  intro f hf
  change |(∫ z, f z ∂Measure.dirac x)-(∫ z, f z ∂Measure.dirac y)| ≤ dist x y
  simpa [Real.dist_eq] using hf.lipschitz.dist_le_mul x y

theorem geometric_dirac_tendsto :
    Tendsto (fun n : ℕ => realDirac ((1/2 : ℝ)^n)) atTop (𝓝 (realDirac 0)) := by
  exact realDirac_lipschitz.continuous.continuousAt.tendsto.comp
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

theorem every_real_firstMoment_cauchy_has_actual_limit
    (μ : ℕ → FirstMomentProbability (0 : ℝ)) (hμ : CauchySeq μ) :
    ∃ ν : FirstMomentProbability (0 : ℝ), Tendsto μ atTop (𝓝 ν) :=
  FirstMomentProbability.cauchySeq_has_limit μ hμ

theorem zero_cost_glued_chain_is_constant
    (μ : ℕ → FirstMomentProbability (0 : ℝ))
    (γ : ∀ n, IntegrableCoupling (μ n).measure (μ (n+1)).measure)
    (hγ : ∀ n, (γ n).cost = 0) : ∀ n, μ n = μ 0 := by
  have hs : Summable (fun n => (γ n).cost) := by
    simpa only [hγ] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  obtain ⟨ν,hb,_⟩ := FirstMomentProbability.exists_limit_of_summable_couplings μ γ hs
  have he (n : ℕ) : μ n = ν := by
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    simpa only [hγ,tsum_zero] using hb n
  intro n
  exact (he n).trans (he 0).symm

end PermanssonResearch.Probability.FirstMomentCompletenessRegression
