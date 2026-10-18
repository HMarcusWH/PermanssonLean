import PermanssonResearch.Perturbation.ContractiveOccupation
import PermanssonResearch.MultipleLimit.FiniteInvariantMeasureTransport

/-! Finite stationary construction for the original all-laws dual contraction.
Existence uses actual Cesaro compactness.  Separation uses scaled singleton
tests on the given metric, without substituting the discrete metric. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace PermanssonResearch.Perturbation.FiniteInvariantConstructor
open PermanssonResearch.Probability
set_option autoImplicit false

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y]

theorem eq_of_dual_zero (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hzero : W1DualLE μ ν 0) : μ = ν := by
  classical
  apply Measure.ext_of_measureReal_singleton
  intro j
  obtain ⟨ε,hε,hsep⟩ := (Metric.isOpen_singleton_iff).1
    (isOpen_discrete ({j} : Set Y))
  let f : Y → ℝ := fun y => if y = j then ε else 0
  have hf : IsKRTest f := by
    refine ⟨measurable_of_finite _, LipschitzWith.of_dist_le_mul ?_, ⟨ε,?_⟩⟩
    · intro a b
      have heq (y : Y) (hy : y ≠ j) : ε ≤ dist y j :=
        le_of_not_gt (fun hh => hy (hsep y hh))
      by_cases ha : a = j <;> by_cases hb : b = j
      · simp [f,ha,hb]
      · simpa [f,ha,hb,Real.dist_eq,abs_of_pos hε,dist_comm] using heq b hb
      · simpa [f,ha,hb,Real.dist_eq,abs_of_pos hε] using heq a ha
      · simp [f,ha,hb]
    · intro y
      dsimp [f]
      split_ifs <;> simp_all [abs_of_pos hε, hε.le]
  have hi (ξ : Measure Y) [IsProbabilityMeasure ξ] :
      (∫ y, f y ∂ξ) = ξ.real {j} * ε := by
    rw [integral_fintype (Integrable.of_finite)]
    simp [f,smul_eq_mul]
  have hh := hzero f hf
  rw [hi μ,hi ν] at hh
  have he : μ.real {j} * ε = ν.real {j} * ε := sub_eq_zero.mp (abs_nonpos_iff.mp hh)
  exact (mul_right_cancel₀ hε.ne') he

variable [Nonempty Y]

theorem finite_dual_bound (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : ∃ c, W1DualLE μ ν c := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  exact ⟨_, W1DualLE.of_integrable_dist μ ν y (Integrable.of_finite) (Integrable.of_finite)⟩

/-- Genuine existence and uniqueness of an invariant probability for every
finite metric kernel satisfying the original dual contraction with rho<1.
No irreducibility, rational weights or aperiodicity are assumed. -/
theorem exists_unique_invariant (K : Kernel Y Y) [IsMarkovKernel K]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hK : IsW1Contraction K ρ) :
    ∃! π : ProbabilityMeasure Y, Kernel.Invariant K π.toMeasure := by
  obtain ⟨π,hπprob,hπinv⟩ :=
    MultipleLimit.FiniteInvariantMeasureTransport.exists_stationary_probability K
  letI : IsProbabilityMeasure π := hπprob
  refine ⟨⟨π,hπprob⟩,hπinv,?_⟩
  intro ν hν
  apply ProbabilityMeasure.toMeasure_injective
  change ν.toMeasure = π
  apply eq_of_dual_zero
  have hb := invariantLaw_wasserstein_le K K ν.toMeasure π hν hπinv hρ0 hρ1 hK
    (fun y => W1DualLE.refl (K y)) (finite_dual_bound ν.toMeasure π)
  simpa using hb

noncomputable def iterateLaw (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : Measure Y) : ℕ → Measure Y
  | 0 => μ
  | n+1 => K ∘ₘ iterateLaw K μ n

instance iterateLaw_probability (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : Measure Y) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (iterateLaw K μ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih =>
    letI := ih
    change IsProbabilityMeasure (K ∘ₘ iterateLaw K μ n)
    infer_instance

theorem geometric_dual_convergence (K : Kernel Y Y) [IsMarkovKernel K]
    {ρ : ℝ} (hK : IsW1Contraction K ρ)
    (μ π : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hπ : K ∘ₘ π = π) {c : ℝ} (hc : W1DualLE μ π c) (n : ℕ) :
    W1DualLE (iterateLaw K μ n) π (ρ^n*c) := by
  induction n with
  | zero => simpa [iterateLaw] using hc
  | succ n ih =>
    have hh := hK (iterateLaw K μ n) π inferInstance inferInstance _ ih
    rw [hπ] at hh
    simpa [iterateLaw,pow_succ,mul_assoc,mul_left_comm,mul_comm] using hh

theorem eventually_arbitrarily_small_dual_bound
    (K : Kernel Y Y) [IsMarkovKernel K]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hK : IsW1Contraction K ρ)
    (μ π : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hπ : K ∘ₘ π = π) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, W1DualLE (iterateLaw K μ n) π ε := by
  obtain ⟨c,hc⟩ := finite_dual_bound μ π
  have hp : Tendsto (fun n : ℕ => ρ^n*c) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const c
  intro ε hε
  filter_upwards [(tendsto_order.1 hp).2 ε hε] with n hn
  exact (geometric_dual_convergence K hK μ π hπ hc n).mono hn.le

end PermanssonResearch.Perturbation.FiniteInvariantConstructor
