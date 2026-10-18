import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Tactic

/-!
# Finite maximal sums and the Hopf integral inequality

No ergodic convergence theorem is assumed. The positive maximal sums are
constructed recursively and their integral inequality follows from actual
measure preservation, including noninvertible transformations.
-/

namespace PermanssonResearch.Probability.Hopf

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω} {f : Ω → ℝ}

def positiveMax (T : Ω → Ω) (f : Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1, ω => max 0 (f ω + positiveMax T f n (T ω))

def partialSum (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, f (T^[k] ω)

theorem partialSum_succ (n : ℕ) (ω : Ω) :
    partialSum T f (n+1) ω = f ω + partialSum T f n (T ω) := by
  unfold partialSum
  rw [Finset.sum_range_succ']
  simp only [Function.iterate_zero_apply, Function.iterate_succ_apply]
  ring

theorem positiveMax_nonneg (n : ℕ) (ω : Ω) : 0 ≤ positiveMax T f n ω := by
  cases n
  · exact le_refl 0
  · exact le_max_left _ _

theorem positiveMax_le_succ (n : ℕ) (ω : Ω) :
    positiveMax T f n ω ≤ positiveMax T f (n+1) ω := by
  induction n generalizing ω with
  | zero => exact positiveMax_nonneg 1 ω
  | succ n ih =>
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T ω)))

theorem positiveMax_monotone (ω : Ω) : Monotone (fun n => positiveMax T f n ω) :=
  monotone_nat_of_le_succ (fun n => positiveMax_le_succ n ω)

theorem partialSum_le_positiveMax (n : ℕ) (ω : Ω) :
    partialSum T f n ω ≤ positiveMax T f n ω := by
  induction n generalizing ω with
  | zero => simp [partialSum, positiveMax]
  | succ n ih =>
    rw [partialSum_succ]
    exact (add_le_add le_rfl (ih (T ω))).trans (le_max_right _ _)

theorem positiveMax_measurable (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (positiveMax T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hT))

theorem positiveMax_integrable (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (positiveMax T f n) μ := by
  induction n with
  | zero => exact integrable_zero Ω ℝ μ
  | succ n ih =>
    exact (integrable_zero Ω ℝ μ).sup (hf.add (hT.integrable_comp_of_integrable ih))

theorem preserving_integral (hT : MeasurePreserving T μ μ) (hg : Measurable f) :
    (∫ ω, f (T ω) ∂μ) = ∫ ω, f ω ∂μ := by
  have he := integral_map (μ := μ) hT.measurable.aemeasurable hg.aestronglyMeasurable
  rw [hT.map_eq] at he
  exact he.symm

theorem indicator_ge_difference (n : ℕ) (ω : Ω) :
    positiveMax T f n ω - positiveMax T f n (T ω) ≤
      {ω | 0 < positiveMax T f n ω}.indicator f ω := by
  classical
  by_cases hp : 0 < positiveMax T f n ω
  · simp only [Set.indicator, Set.mem_setOf_eq, if_pos hp]
    cases n with
    | zero => exact False.elim (lt_irrefl 0 hp)
    | succ n =>
      have ha : 0 < f ω + positiveMax T f n (T ω) :=
        (lt_max_iff.mp hp).resolve_left (lt_irrefl 0)
      rw [positiveMax, max_eq_right ha.le]
      linarith [positiveMax_le_succ (T := T) (f := f) n (T ω)]
  · simp only [Set.indicator, Set.mem_setOf_eq, if_neg hp]
    have hz : positiveMax T f n ω = 0 :=
      le_antisymm (le_of_not_gt hp) (positiveMax_nonneg n ω)
    rw [hz, zero_sub]
    exact neg_nonpos.mpr (positiveMax_nonneg n (T ω))

/-- The finite Hopf inequality is derived by integrating a pointwise coboundary. -/
theorem finite_maximal_integral_nonneg (hT : MeasurePreserving T μ μ)
    (hf : Measurable f) (hfi : Integrable f μ) (n : ℕ) :
    0 ≤ ∫ ω, {ω | 0 < positiveMax T f n ω}.indicator f ω ∂μ := by
  have hm := positiveMax_measurable hT.measurable hf n
  have hi := positiveMax_integrable hT hfi n
  have hic := hT.integrable_comp_of_integrable hi
  have hevent : MeasurableSet {ω | 0 < positiveMax T f n ω} :=
    measurableSet_lt measurable_const hm
  have hind := hfi.indicator hevent
  have hh := integral_mono (hi.sub hic) hind (indicator_ge_difference (T := T) (f := f) n)
  change (∫ x, positiveMax T f n x - positiveMax T f n (T x) ∂μ) ≤ _ at hh
  have he : (∫ x, positiveMax T f n x - positiveMax T f n (T x) ∂μ) = 0 := by
    calc
      _ = (∫ x, positiveMax T f n x ∂μ) -
          (∫ x, positiveMax T f n (T x) ∂μ) := by
        simpa only [Function.comp_apply] using integral_sub hi hic
      _ = 0 := by rw [preserving_integral hT hm, sub_self]
  rw [he] at hh
  exact hh

/-- If some forward partial sum is positive at every point, its integral is
nonnegative. This is the maximal inequality used in the bounded Birkhoff proof. -/
theorem integral_nonneg_of_positive_partial_sums (hT : MeasurePreserving T μ μ)
    (hf : Measurable f) (hfi : Integrable f μ)
    (hpos : ∀ ω, ∃ n, 0 < partialSum T f n ω) : 0 ≤ ∫ ω, f ω ∂μ := by
  classical
  have hlim : ∀ ω, Tendsto
      (fun n => {ω | 0 < positiveMax T f n ω}.indicator f ω) atTop (𝓝 (f ω)) := by
    intro ω
    obtain ⟨n,hn⟩ := hpos ω
    have hp := hn.trans_le (partialSum_le_positiveMax (T := T) (f := f) n ω)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with k hk
    have hpk : 0 < positiveMax T f k ω :=
      hp.trans_le (positiveMax_monotone (T := T) (f := f) ω hk)
    simp only [Set.indicator, Set.mem_setOf_eq, if_pos hpk]
  have ht := tendsto_integral_of_dominated_convergence (fun ω => ‖f ω‖)
    (fun n => (hf.indicator (measurableSet_lt measurable_const
      (positiveMax_measurable hT.measurable hf n))).aestronglyMeasurable)
    hfi.norm
    (fun n => Filter.Eventually.of_forall fun ω => by
      by_cases h : 0 < positiveMax T f n ω <;> simp [Set.indicator, h])
    (Filter.Eventually.of_forall hlim)
  exact ge_of_tendsto ht (Filter.Eventually.of_forall (finite_maximal_integral_nonneg hT hf hfi))

end
end PermanssonResearch.Probability.Hopf
