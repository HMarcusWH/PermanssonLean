import PermanssonResearch.MultipleLimit.RegenerativeDescriptorMoments

/-! Actual distance-tail control, rather than inferring first-moment
convergence from weak convergence alone. The empirical excess tails vanish
uniformly over all positive horizons on almost every original path. -/

open MeasureTheory ProbabilityTheory Filter Finset TopologicalSpace
open scoped Topology ProbabilityTheory
namespace PermanssonResearch.MultipleLimit.RegenerativeDescriptorTails
open FiniteCanonicalPath RegenerativeIntegrable RegenerativeDescriptorMoments
open PermanssonResearch.Probability PermanssonResearch.Probability.Regenerative
set_option autoImplicit false
variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V] [SeparableSpace V]

def tail (v₀ : V) (M : ℕ) (v : V) : ℝ := max (dist v v₀-(M : ℝ)) 0

theorem tail_nonneg (v₀ : V) (M : ℕ) (v : V) : 0 ≤ tail v₀ M v := le_max_right _ _

theorem tail_le_distance (v₀ : V) (M : ℕ) (v : V) : tail v₀ M v ≤ dist v v₀ := by
  apply max_le
  · linarith [Nat.cast_nonneg (α := ℝ) M]
  · exact dist_nonneg

theorem tail_measurable (v₀ : V) (M : ℕ) : Measurable (tail v₀ M) :=
  ((measurable_id.dist measurable_const).sub measurable_const).max measurable_const

theorem tail_integrable (v₀ : V) (ν : FirstMomentProbability v₀) (M : ℕ) :
    Integrable (tail v₀ M) ν.measure :=
  ν.firstMoment.mono' (tail_measurable v₀ M).aestronglyMeasurable (ae_of_all _ fun v => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (tail_nonneg v₀ M v)] using tail_le_distance v₀ M v)

theorem tail_integral_tendsto_zero (v₀ : V) (ν : FirstMomentProbability v₀) :
    Tendsto (fun M => ∫ v, tail v₀ M v ∂ν.measure) atTop (𝓝 0) := by
  have hp (v : V) : Tendsto (fun M => tail v₀ M v) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    have he : ∀ᶠ M : ℕ in atTop, dist v v₀ ≤ (M : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (dist v v₀))
    filter_upwards [he] with M hM
    exact (max_eq_right (sub_nonpos.mpr hM)).symm
  have ht := tendsto_integral_of_dominated_convergence (fun v => dist v v₀)
    (fun M => (tail_measurable v₀ M).aestronglyMeasurable) ν.firstMoment
    (fun M => ae_of_all _ fun v => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (tail_nonneg v₀ M v)] using tail_le_distance v₀ M v)
    (ae_of_all _ hp)
  simpa using! ht

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] [Nonempty V]

theorem tail_averages (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (h : Y → V) (hh : Measurable h) (v₀ : V)
    (hbudget : RegenerativeMoment.RewardCondition R ξ r (fun y => dist (h y) v₀)) (M : ℕ) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => (∑ t ∈ range (n+1), tail v₀ M (h (w t)))/((n+1 : ℕ) : ℝ))
        atTop (𝓝 (∫ v, tail v₀ M v ∂(target R ξ hr hr1 h hh v₀ hbudget).measure)) := by
  have hd := RegenerativeMoment.integrable_law_of_rewardCondition R ξ hr hr1
    (hh.dist measurable_const) hbudget
  have hf : Measurable (fun y => tail v₀ M (h y)) := (tail_measurable v₀ M).comp hh
  have hfi : Integrable (fun y => tail v₀ M (h y)) (law R ξ r) :=
    hd.mono' hf.aestronglyMeasurable (ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (tail_nonneg v₀ M (h y))]
        using tail_le_distance v₀ M (h y))
  rw [target_integral R ξ hr hr1 h hh v₀ hbudget (tail_measurable v₀ M)]
  exact canonical_nonnegative_integrable_averages R K ξ μ hr hr1 hmix _ hf
    (fun y => tail_nonneg v₀ M (h y)) hfi

theorem canonical_excess_tail_uniform
    (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (h : Y → V) (hh : Measurable h) (v₀ : V)
    (hbudget : RegenerativeMoment.RewardCondition R ξ r (fun y => dist (h y) v₀)) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure, ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ n : ℕ,
      (∑ t ∈ range (n+1), tail v₀ M (h (w t)))/((n+1 : ℕ) : ℝ) < ε := by
  have hall := ae_all_iff.mpr (fun M => tail_averages R K ξ μ hr hr1 hmix h hh v₀ hbudget M)
  filter_upwards [hall] with w hw
  intro ε hε
  have hlim := tail_integral_tendsto_zero v₀ (target R ξ hr hr1 h hh v₀ hbudget)
  obtain ⟨M,hM⟩ := ((tendsto_order.mp hlim).2 ε hε).exists
  have hev := (tendsto_order.mp (hw M)).2 ε hM
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  let C : ℝ := ∑ t ∈ range (N+1), dist (h (w t)) v₀
  obtain ⟨m,hm⟩ := exists_nat_ge C
  refine ⟨max M m,?_⟩
  intro n
  by_cases hn : N ≤ n
  · apply lt_of_le_of_lt _ (hN n hn)
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply sum_le_sum
    intro t ht
    apply max_le_max _ le_rfl
    apply sub_le_sub_left
    exact_mod_cast Nat.le_max_left M m
  · have hz : (∑ t ∈ range (n+1), tail v₀ (max M m) (h (w t))) = 0 := by
      apply sum_eq_zero
      intro t ht
      have htN : t ∈ range (N+1) := mem_range.mpr (by have := mem_range.mp ht; omega)
      have hd : dist (h (w t)) v₀ ≤ C :=
        single_le_sum (fun s _ => (dist_nonneg : 0 ≤ dist (h (w s)) v₀)) htN
      have hmax : (m : ℝ) ≤ (max M m : ℕ) := by exact_mod_cast Nat.le_max_right M m
      exact max_eq_right (sub_nonpos.mpr (hd.trans (hm.trans hmax)))
    rw [hz,zero_div]
    exact hε

/-- The usual distance-times-tail-indicator criterion follows from the
proved excess-tail bound, uniformly over every positive empirical horizon. -/
theorem canonical_distance_tail_uniform
    (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (h : Y → V) (hh : Measurable h) (v₀ : V)
    (hbudget : RegenerativeMoment.RewardCondition R ξ r (fun y => dist (h y) v₀)) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure, ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ n : ℕ,
      (∑ t ∈ range (n+1), if (M : ℝ) < dist (h (w t)) v₀
        then dist (h (w t)) v₀ else 0)/((n+1 : ℕ) : ℝ) < ε := by
  classical
  filter_upwards [canonical_excess_tail_uniform R K ξ μ hr hr1 hmix h hh v₀ hbudget]
    with w hw
  intro ε hε
  obtain ⟨m,hm⟩ := hw (ε/2) (by positivity)
  refine ⟨2*m,fun n => ?_⟩
  have hb : (∑ t ∈ range (n+1), if ((2*m : ℕ) : ℝ) < dist (h (w t)) v₀
        then dist (h (w t)) v₀ else 0) ≤
      2*(∑ t ∈ range (n+1), tail v₀ m (h (w t))) := by
    rw [mul_sum]
    apply sum_le_sum
    intro t ht
    split_ifs with hd
    · simp only [Nat.cast_mul,Nat.cast_ofNat] at hd
      have he := le_max_left (dist (h (w t)) v₀-(m : ℝ)) 0
      change dist (h (w t)) v₀ ≤ 2*max (dist (h (w t)) v₀-(m : ℝ)) 0
      linarith
    · exact mul_nonneg (by norm_num) (tail_nonneg v₀ m (h (w t)))
  have hpos : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hh := div_le_div_of_nonneg_right hb hpos.le
  rw [mul_div_assoc] at hh
  exact hh.trans_lt (by linarith [hm n])

end PermanssonResearch.MultipleLimit.RegenerativeDescriptorTails
