import PermanssonResearch.Probability.HopfMaximal
import PermanssonResearch.Probability.BoundedOrbitAverages
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The maximal inequality for integrable observables, derived from the
finite Hopf inequality. It supplies uniform-in-time L1 approximation control. -/

open MeasureTheory Filter Set
open scoped Topology

namespace PermanssonResearch.Probability.Hopf

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {T : Ω → Ω} {f g : Ω → ℝ}

def maximalEvent (T : Ω → Ω) (f : Ω → ℝ) : Set Ω :=
  {ω | ∃ n, 0 < positiveMax T f n ω}

theorem maximalEvent_measurable (hT : Measurable T) (hf : Measurable f) :
    MeasurableSet (maximalEvent T f) := by
  change MeasurableSet {ω | ∃ n, 0 < positiveMax T f n ω}
  simp_rw [setOf_exists]
  exact MeasurableSet.iUnion (fun n =>
    measurableSet_lt measurable_const (positiveMax_measurable hT hf n))

theorem maximal_integral_nonneg (hT : MeasurePreserving T μ μ)
    (hf : Measurable f) (hfi : Integrable f μ) :
    0 ≤ ∫ ω, (maximalEvent T f).indicator f ω ∂μ := by
  classical
  have hm n : MeasurableSet {ω | 0 < positiveMax T f n ω} :=
    measurableSet_lt measurable_const (positiveMax_measurable hT.measurable hf n)
  have ht : ∀ ω, Tendsto
      (fun n => {ω | 0 < positiveMax T f n ω}.indicator f ω) atTop
      (𝓝 ((maximalEvent T f).indicator f ω)) := by
    intro ω
    by_cases hw : ω ∈ maximalEvent T f
    · obtain ⟨n, hn⟩ := hw
      have hmem : ω ∈ maximalEvent T f := ⟨n, hn⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with k hk
      have hp := hn.trans_le (positiveMax_monotone (T := T) (f := f) ω hk)
      simp [Set.indicator, hmem, hp]
    · have hn (n : ℕ) : ¬ 0 < positiveMax T f n ω := fun hh => hw ⟨n, hh⟩
      simpa [Set.indicator, hw, hn] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hi := tendsto_integral_of_dominated_convergence (fun ω => ‖f ω‖)
    (fun n => (hf.indicator (hm n)).aestronglyMeasurable) hfi.norm
    (fun n => ae_of_all _ (fun ω => by
      by_cases hh : 0 < positiveMax T f n ω <;> simp [Set.indicator, hh]))
    (ae_of_all _ ht)
  exact ge_of_tendsto hi (Eventually.of_forall (finite_maximal_integral_nonneg hT hf hfi))

theorem maximalEvent_measure_bound (hT : MeasurePreserving T μ μ)
    (hg : Measurable g) (hgi : Integrable g μ) (hg0 : ∀ ω, 0 ≤ g ω)
    {ε : ℝ} (hε : 0 < ε) :
    ε * μ.real (maximalEvent T (fun ω => g ω - ε)) ≤ ∫ ω, g ω ∂μ := by
  let E := maximalEvent T (fun ω => g ω - ε)
  have hE : MeasurableSet E := maximalEvent_measurable hT.measurable (hg.sub measurable_const)
  have hn := maximal_integral_nonneg hT (hg.sub measurable_const)
    (hgi.sub (integrable_const ε))
  have he : (∫ ω, E.indicator (fun ω => g ω - ε) ω ∂μ) =
      (∫ ω, E.indicator g ω ∂μ) - ε * μ.real E := by
    rw [show E.indicator (fun ω => g ω - ε) =
      E.indicator g - E.indicator (fun _ => ε) by ext ω; simp [Set.indicator]; split_ifs <;> ring]
    simp only [Pi.sub_apply]
    rw [integral_sub (hgi.indicator hE) ((integrable_const ε).indicator hE),
      integral_indicator_const _ hE]
    simp [smul_eq_mul, mul_comm]
  change 0 ≤ ∫ ω, E.indicator (fun ω => g ω - ε) ω ∂μ at hn
  rw [he] at hn
  have hu : (∫ ω, E.indicator g ω ∂μ) ≤ ∫ ω, g ω ∂μ := by
    apply integral_mono (hgi.indicator hE) hgi
    intro ω
    by_cases hh : ω ∈ E <;> simp [Set.indicator, hh, hg0 ω]
  dsimp [E] at *
  linarith

theorem average_gt_mem_maximalEvent (g : Ω → ℝ) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) (ω : Ω) (hh : ε < birkhoffAverage ℝ T g n ω) :
    ω ∈ maximalEvent T (fun ω => g ω - ε) := by
  have hn : n ≠ 0 := by
    intro hz
    subst n
    have hbad : ε < 0 := by simpa using hh
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : partialSum T (fun ω => g ω - ε) n ω =
      (n : ℝ) * (birkhoffAverage ℝ T g n ω - ε) := by
    simp only [partialSum, birkhoffAverage, birkhoffSum, smul_eq_mul,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hp : 0 < partialSum T (fun ω => g ω - ε) n ω := by
    rw [he]
    exact mul_pos hnR (sub_pos.mpr hh)
  exact ⟨n, hp.trans_le
    (partialSum_le_positiveMax (T := T) (f := fun ω => g ω - ε) n ω)⟩

theorem average_sub_abs_le (T : Ω → Ω) (f g : Ω → ℝ) (n : ℕ) (ω : Ω) :
    |birkhoffAverage ℝ T f n ω - birkhoffAverage ℝ T g n ω| ≤
      birkhoffAverage ℝ T (fun ω => |f ω - g ω|) n ω := by
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul, ← mul_sub, ← Finset.sum_sub_distrib]
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

end
end PermanssonResearch.Probability.Hopf
