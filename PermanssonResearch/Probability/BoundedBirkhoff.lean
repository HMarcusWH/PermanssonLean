import PermanssonResearch.Probability.HopfMaximal
import PermanssonResearch.Probability.BoundedOrbitAverages

/-!+# Bounded pointwise ergodic convergence from the maximal inequality

The limit is the measurable, exactly invariant upper orbit average. The proof
derives its integral bound from the Hopf inequality and forces the upper and
lower orbit averages to coincide almost everywhere. No pointwise ergodic
convergence theorem is used as a hypothesis.
-/

namespace PermanssonResearch.Probability.Hopf

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {T : Ω → Ω} {f : Ω → ℝ}

theorem integrable_of_abs_bound (hf : Measurable f) (M : ℝ)
    (hb : ∀ ω, |f ω| ≤ M) : Integrable f μ := by
  apply (integrable_const M).mono' hf.aestronglyMeasurable
  exact Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb ω

theorem upperAverage_integrable (hT : Measurable T) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ ω, |f ω| ≤ M) :
    Integrable (upperAverage T f) μ :=
  integrable_of_abs_bound (upperAverage_measurable hT hf) M
    (upperAverage_abs_bound M hM hb)

theorem positive_partial_sum_sub_upper (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ ω, |f ω| ≤ M) {ε : ℝ} (hε : 0 < ε) (ω : Ω) :
    ∃ n, 0 < partialSum T (f - fun ω => upperAverage T f ω - ε) n ω := by
  have hl := average_bddBelow (T := T) M hM hb ω
  have hfreq := frequently_lt_of_lt_limsup hl.isCoboundedUnder_le
    (show upperAverage T f ω - ε < upperAverage T f ω by linarith)
  obtain ⟨n, hn, ha⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
  have hnR : 0 < (n : ℝ) := by exact_mod_cast ha
  have hinv : (fun ω => upperAverage T f ω - ε) ∘ T =
      (fun ω => upperAverage T f ω - ε) := by
    funext x
    simp only [Function.comp_apply, upperAverage_invariant M hM hb]
  have hg : 0 < birkhoffAverage ℝ T (f - fun ω => upperAverage T f ω - ε) n ω := by
    rw [birkhoffAverage_sub_apply,
      birkhoffAverage_apply_of_comp_eq ℝ hinv (ne_of_gt hnR)]
    linarith
  refine ⟨n, ?_⟩
  change 0 < (n : ℝ)⁻¹ * partialSum T (f - fun ω => upperAverage T f ω - ε) n ω at hg
  have hi : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnR
  nlinarith

theorem integral_upperAverage_le (hT : MeasurePreserving T μ μ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ ω, |f ω| ≤ M) :
    (∫ ω, upperAverage T f ω ∂μ) ≤ ∫ ω, f ω ∂μ := by
  have hfi : Integrable f μ := integrable_of_abs_bound hf M hb
  have hui := upperAverage_integrable (μ := μ) hT.measurable hf M hM hb
  have hu := upperAverage_measurable hT.measurable hf
  have he : ∀ ε > 0, (∫ ω, upperAverage T f ω ∂μ) ≤ (∫ ω, f ω ∂μ) + ε := by
    intro ε hε
    have hg := integral_nonneg_of_positive_partial_sums hT
      (hf.sub (hu.sub measurable_const)) (hfi.sub (hui.sub (integrable_const ε)))
      (positive_partial_sum_sub_upper M hM hb hε)
    have hi : (∫ ω, (f - fun ω => upperAverage T f ω - ε) ω ∂μ) =
        (∫ ω, f ω ∂μ) - ((∫ ω, upperAverage T f ω ∂μ) - ε) := by
      calc
        _ = (∫ ω, f ω ∂μ) - (∫ ω, upperAverage T f ω - ε ∂μ) :=
          integral_sub hfi (hui.sub (integrable_const ε))
        _ = _ := by rw [integral_sub hui (integrable_const ε)]; simp
    have hg' : 0 ≤ ∫ ω, (f - fun ω => upperAverage T f ω - ε) ω ∂μ := hg
    rw [hi] at hg'
    linarith
  by_contra h
  have hp : 0 < ((∫ ω, upperAverage T f ω ∂μ) - (∫ ω, f ω ∂μ))/2 := by linarith
  have hh := he _ hp
  linarith

theorem upperAverage_neg_eq_neg_liminf (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ ω, |f ω| ≤ M) (ω : Ω) :
    upperAverage T (-f) ω = -liminf (fun n => birkhoffAverage ℝ T f n ω) atTop := by
  have hu := average_bddAbove (T := T) M hM hb ω
  have hl := average_bddBelow (T := T) M hM hb ω
  unfold upperAverage
  simp only [birkhoffAverage_neg_apply]
  simpa only [zero_sub] using
    limsup_const_sub atTop (fun n => birkhoffAverage ℝ T f n ω) 0 hu.isCoboundedUnder_ge hl

/-- Actual almost-everywhere convergence for every bounded measurable real
observable of a probability-preserving transformation, including noninvertible
transformations and transformations without an ergodicity assumption. -/
theorem bounded_birkhoff (hT : MeasurePreserving T μ μ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ ω, |f ω| ≤ M) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n ω) atTop
      (𝓝 (upperAverage T f ω)) := by
  have hnb : ∀ ω, |(-f) ω| ≤ M := fun ω => by simpa only [Pi.neg_apply, abs_neg] using hb ω
  have hui := upperAverage_integrable (μ := μ) hT.measurable hf M hM hb
  have hvi := upperAverage_integrable (μ := μ) hT.measurable hf.neg M hM hnb
  have hgap : ∀ ω, 0 ≤ upperAverage T f ω + upperAverage T (-f) ω := by
    intro ω
    rw [upperAverage_neg_eq_neg_liminf M hM hb]
    exact sub_nonneg.mpr (liminf_le_limsup (average_bddAbove M hM hb ω)
      (average_bddBelow M hM hb ω))
  have hzero : (∫ ω, upperAverage T f ω + upperAverage T (-f) ω ∂μ) = 0 := by
    apply le_antisymm
    · rw [integral_add hui hvi]
      have h1 := integral_upperAverage_le hT hf M hM hb
      have h2 := integral_upperAverage_le hT hf.neg M hM hnb
      simp only [Pi.neg_apply, integral_neg] at h2
      linarith
    · exact integral_nonneg hgap
  have hae := (integral_eq_zero_iff_of_nonneg hgap (hui.add hvi)).mp hzero
  filter_upwards [hae] with ω hω
  have hi : liminf (fun n => birkhoffAverage ℝ T f n ω) atTop = upperAverage T f ω := by
    have hn := upperAverage_neg_eq_neg_liminf (T := T) M hM hb ω
    change upperAverage T f ω + upperAverage T (-f) ω = 0 at hω
    linarith
  exact tendsto_of_liminf_eq_limsup hi rfl (average_bddAbove M hM hb ω)
    (average_bddBelow M hM hb ω)

end
end PermanssonResearch.Probability.Hopf
