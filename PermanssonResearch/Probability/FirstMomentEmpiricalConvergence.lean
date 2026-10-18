import PermanssonResearch.Probability.FiniteQuantizationBound
import PermanssonResearch.Probability.FirstMomentEmpirical

/-! Literal empirical laws converge in the genuine first-moment metric from
countably many actual scalar averages. No W1 or uniform-integrability limit
is a hypothesis. -/

open MeasureTheory Filter TopologicalSpace
open scoped Topology BigOperators

namespace PermanssonResearch.Probability.FirstMomentEmpirical

noncomputable section
variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V]
  [SeparableSpace V] [Nonempty V]
open FirstMomentQuantization

theorem empirical_tendsto_of_quantized_averages (v0 : V)
    (π : FirstMomentProbability v0) (w : ℕ → V)
    (herr : ∀ k, Tendsto
      (fun n => (∑ t ∈ Finset.range (n+1), error v0 k (w t))/((n+1 : ℕ) : ℝ))
      atTop (𝓝 (∫ v, error v0 k v ∂π.measure)))
    (hcell : ∀ k (i : Fin (k+1)), Tendsto
      (fun n => (∑ t ∈ Finset.range (n+1), cellIndicator v0 k i (w t))/((n+1 : ℕ) : ℝ))
      atTop (𝓝 (∫ v, cellIndicator v0 k i v ∂π.measure))) :
    Tendsto (fun n => empirical v0 n w) atTop (𝓝 π) := by
  have hπ := integral_error_tendsto π.measure v0 π.firstMoment
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,hk⟩ := ((tendsto_order.mp hπ).2 (ε/4) (by positivity)).exists
  have he : Tendsto (fun n => ∫ v, error v0 k v ∂(empirical v0 n w).measure)
      atTop (𝓝 (∫ v, error v0 k v ∂π.measure)) := by
    simp_rw [empirical_integral _ _ _ _ (error_measurable v0 k)]
    exact herr k
  have hi (i : Fin (k+1)) : Tendsto
      (fun n => ∫ v, cellIndicator v0 k i v ∂(empirical v0 n w).measure)
      atTop (𝓝 (∫ v, cellIndicator v0 k i v ∂π.measure)) := by
    simp_rw [empirical_integral _ _ _ _ (cellIndicator_measurable v0 k i)]
    exact hcell k i
  have hs : Tendsto
      (fun n => ∑ i : Fin (k+1), dist (center v0 k i) v0 *
        |(∫ v, cellIndicator v0 k i v ∂(empirical v0 n w).measure)-
          (∫ v, cellIndicator v0 k i v ∂π.measure)|) atTop (𝓝 0) := by
    have h := tendsto_finset_sum Finset.univ (fun i _ =>
      ((hi i).sub (tendsto_const_nhds
        (x := ∫ v, cellIndicator v0 k i v ∂π.measure))).abs.const_mul
          (dist (center v0 k i) v0))
    simpa using h
  have hb := (he.add (tendsto_const_nhds (x := ∫ v, error v0 k v ∂π.measure))).add hs
  have hbound : ∀ᶠ n in atTop,
      (∫ v, error v0 k v ∂(empirical v0 n w).measure)+
        (∫ v, error v0 k v ∂π.measure)+
        (∑ i : Fin (k+1), dist (center v0 k i) v0 *
          |(∫ v, cellIndicator v0 k i v ∂(empirical v0 n w).measure)-
            (∫ v, cellIndicator v0 k i v ∂π.measure)|) < ε :=
    (tendsto_order.mp hb).2 ε (by linarith)
  filter_upwards [hbound] with n hn
  exact (distance_le_quantization v0 (empirical v0 n w) π k).trans_lt hn

/-- Countable scalar almost-sure statements are combined before invoking the
deterministic quantization theorem. No uncountable family of null sets occurs. -/
theorem ae_empirical_tendsto_of_quantized_averages (v0 : V)
    (π : FirstMomentProbability v0) (ρ : Measure (ℕ → V))
    (herr : ∀ k, ∀ᵐ w ∂ρ, Tendsto
      (fun n => (∑ t ∈ Finset.range (n+1), error v0 k (w t))/((n+1 : ℕ) : ℝ))
      atTop (𝓝 (∫ v, error v0 k v ∂π.measure)))
    (hcell : ∀ k (i : Fin (k+1)), ∀ᵐ w ∂ρ, Tendsto
      (fun n => (∑ t ∈ Finset.range (n+1), cellIndicator v0 k i (w t))/((n+1 : ℕ) : ℝ))
      atTop (𝓝 (∫ v, cellIndicator v0 k i v ∂π.measure))) :
    ∀ᵐ w ∂ρ, Tendsto (fun n => empirical v0 n w) atTop (𝓝 π) := by
  have he := ae_all_iff.mpr herr
  have hc := ae_all_iff.mpr (fun k => ae_all_iff.mpr (hcell k))
  filter_upwards [he,hc] with w hwerr hwcell
  exact empirical_tendsto_of_quantized_averages v0 π w hwerr hwcell

end
end PermanssonResearch.Probability.FirstMomentEmpirical
