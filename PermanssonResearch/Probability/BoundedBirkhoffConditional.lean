import PermanssonResearch.Probability.BoundedBirkhoff
import PermanssonResearch.Probability.InvariantSigma
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! The actual bounded orbit limit equals conditional expectation on the
invariant sigma-algebra. Set-integral identification is derived from measure
preservation and dominated convergence. -/

namespace PermanssonResearch.Probability.Hopf

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {T : Ω → Ω} {f : Ω → ℝ}

theorem invariant_set_average_integral (hT : MeasurePreserving T μ μ)
    (hf : Measurable f) (hfi : Integrable f μ) {s : Set Ω}
    (hs : MeasurableSet[invariantSigma T] s) {n : ℕ} (hn : n ≠ 0) :
    (∫ ω in s, birkhoffAverage ℝ T f n ω ∂μ) = ∫ ω in s, f ω ∂μ := by
  have hTs : MeasurePreserving T (μ.restrict s) (μ.restrict s) := by
    simpa only [hs.2] using hT.restrict_preimage hs.1
  have hi (k : ℕ) : Integrable (fun ω => f (T^[k] ω)) (μ.restrict s) :=
    (hTs.iterate k).integrable_comp_of_integrable hfi.restrict
  have he (k : ℕ) : (∫ ω in s, f (T^[k] ω) ∂μ) = ∫ ω in s, f ω ∂μ :=
    preserving_integral (hTs.iterate k) hf
  unfold birkhoffAverage birkhoffSum
  simp only [smul_eq_mul]
  rw [integral_const_mul, integral_finset_sum _ fun k _ => hi k]
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [← mul_assoc, inv_mul_cancel₀ hnR, one_mul]

theorem invariant_set_upperAverage_integral (hT : MeasurePreserving T μ μ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ ω, |f ω| ≤ M)
    {s : Set Ω} (hs : MeasurableSet[invariantSigma T] s) :
    (∫ ω in s, upperAverage T f ω ∂μ) = ∫ ω in s, f ω ∂μ := by
  have hfi : Integrable f μ := integrable_of_abs_bound hf M hb
  have hl := tendsto_integral_of_dominated_convergence (μ := μ.restrict s) (fun _ => M)
    (fun n => (average_measurable hT.measurable hf n).aestronglyMeasurable)
    (integrable_const M)
    (fun n => Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using average_abs_bound M hM hb n ω)
    (ae_restrict_of_ae (bounded_birkhoff hT hf M hM hb))
  have hc : Tendsto (fun n => ∫ ω in s, birkhoffAverage ℝ T f n ω ∂μ)
      atTop (𝓝 (∫ ω in s, f ω ∂μ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (invariant_set_average_integral hT hf hfi hs (by omega)).symm
  exact tendsto_nhds_unique hl hc

theorem upperAverage_ae_condExp (hT : MeasurePreserving T μ μ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ ω, |f ω| ≤ M) :
    upperAverage T f =ᵐ[μ] μ[f | invariantSigma T] := by
  apply ae_eq_condExp_of_forall_setIntegral_eq (invariantSigma_le T)
    (integrable_of_abs_bound hf M hb)
  · intro s hs hμs
    exact (upperAverage_integrable (μ := μ) hT.measurable hf M hM hb).integrableOn
  · intro s hs hμs
    exact invariant_set_upperAverage_integral hT hf M hM hb hs
  · exact (upperAverage_measurable_invariant hT.measurable hf M hM hb).aestronglyMeasurable

theorem bounded_birkhoff_condExp (hT : MeasurePreserving T μ μ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ ω, |f ω| ≤ M) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n ω) atTop
      (𝓝 ((μ[f | invariantSigma T]) ω)) := by
  filter_upwards [bounded_birkhoff hT hf M hM hb,
    upperAverage_ae_condExp hT hf M hM hb] with ω hω he
  rwa [he] at hω

end
end PermanssonResearch.Probability.Hopf
