import PermanssonResearch.Probability.L1AverageApproximation

/-! Nonnegative integrable observables are approximated by actual bounded
truncations. No moment convergence is assumed in the average-limit theorem. -/

open MeasureTheory Filter Set
open scoped Topology

namespace PermanssonResearch.Probability.Hopf

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def positiveTruncation (f : Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := min (f ω) k

theorem positiveTruncation_measurable {f : Ω → ℝ} (hf : Measurable f) (k : ℕ) :
    Measurable (positiveTruncation f k) := hf.min measurable_const

theorem positiveTruncation_bound {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (k : ℕ) (ω : Ω) :
    |positiveTruncation f k ω| ≤ k := by
  unfold positiveTruncation
  rw [abs_of_nonneg (le_min (hf0 ω) (Nat.cast_nonneg k))]
  exact min_le_right _ _

theorem positiveTruncation_integrable {f : Ω → ℝ} (hfi : Integrable f μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (k : ℕ) : Integrable (positiveTruncation f k) μ := by
  exact hfi.inf (integrable_const (k : ℝ))

theorem positiveTruncation_tendsto (f : Ω → ℝ) (ω : Ω) :
    Tendsto (fun k => positiveTruncation f k ω) atTop (𝓝 (f ω)) := by
  have he : ∀ᶠ k : ℕ in atTop, f ω ≤ (k : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (f ω))
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with k hk
  exact (min_eq_left hk).symm

theorem positiveTruncation_L1 {f : Ω → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (hf0 : ∀ ω, 0 ≤ f ω) :
    Tendsto (fun k => ∫ ω, |f ω - positiveTruncation f k ω| ∂μ) atTop (𝓝 0) := by
  have hp (ω : Ω) : Tendsto (fun k => |f ω - positiveTruncation f k ω|) atTop (𝓝 (0 : ℝ)) := by
    have hh : Tendsto (fun k : ℕ => f ω - positiveTruncation f k ω)
        atTop (𝓝 (f ω - f ω)) :=
      tendsto_const_nhds.sub (positiveTruncation_tendsto f ω)
    simpa using hh.abs
  have ht := tendsto_integral_of_dominated_convergence (fun ω => ‖f ω‖)
    (fun k => by
      have hm : Measurable (fun ω => |f ω - positiveTruncation f k ω|) := by
        simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hf.sub (positiveTruncation_measurable hf k)).norm
      exact hm.aestronglyMeasurable)
    hfi.norm
    (fun k => ae_of_all _ (fun ω => by
      have hmin : 0 ≤ positiveTruncation f k ω := le_min (hf0 ω) (Nat.cast_nonneg k)
      have hle : positiveTruncation f k ω ≤ f ω := min_le_left _ _
      simp only [Real.norm_eq_abs, abs_abs]
      rw [abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonneg (hf0 ω)]
      linarith))
    (ae_of_all _ hp)
  simpa using ht

theorem positiveTruncation_integral_tendsto {f : Ω → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (hf0 : ∀ ω, 0 ≤ f ω) :
    Tendsto (fun k => ∫ ω, positiveTruncation f k ω ∂μ) atTop (𝓝 (∫ ω, f ω ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun ω => ‖f ω‖)
    (fun k => (positiveTruncation_measurable hf k).aestronglyMeasurable) hfi.norm
  · intro k
    apply ae_of_all
    intro ω
    unfold positiveTruncation
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_min (hf0 ω) (Nat.cast_nonneg k)), abs_of_nonneg (hf0 ω)]
    exact min_le_left _ _
  · exact ae_of_all _ (positiveTruncation_tendsto f)

theorem ae_nonnegative_average_limit {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (f : Ω → ℝ) (hf : Measurable f) (hfi : Integrable f μ) (hf0 : ∀ ω, 0 ≤ f ω)
    (hav : ∀ k, ∀ᵐ ω ∂μ,
      Tendsto (fun n => birkhoffAverage ℝ T (positiveTruncation f k) n ω)
        atTop (𝓝 (∫ ω, positiveTruncation f k ω ∂μ))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n ω)
      atTop (𝓝 (∫ ω, f ω ∂μ)) :=
  ae_average_limit_of_L1_approximation hT f hf hfi (positiveTruncation f)
    (positiveTruncation_measurable hf) (positiveTruncation_integrable hfi hf0)
    _ _ (positiveTruncation_L1 hf hfi hf0) (positiveTruncation_integral_tendsto hf hfi hf0) hav

end
end PermanssonResearch.Probability.Hopf
