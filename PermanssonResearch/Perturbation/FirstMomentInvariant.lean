import PermanssonResearch.Perturbation.FirstMomentKernel
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Probability.Kernel.Invariance

/-! Automatic invariant-law construction for first-moment-preserving kernels
satisfying the original global all-probability-law dual contraction. -/

open MeasureTheory ProbabilityTheory TopologicalSpace Filter Function
open scoped Topology
namespace PermanssonResearch.Perturbation.FirstMomentInvariant
open PermanssonResearch.Probability
set_option autoImplicit false

variable {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [MeasurableSpace Y]
variable [BorelSpace Y] [SeparableSpace Y]

noncomputable def anchor (y₀ : Y) : FirstMomentProbability y₀ :=
  ⟨⟨Measure.dirac y₀,inferInstance⟩,integrable_dirac (by simp)⟩

theorem push_contracting (K : Kernel Y Y) [IsMarkovKernel K] {y₀ : Y}
    (hM : PreservesFirstMoment K y₀) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : IsW1Contraction K ρ) : ContractingWith ⟨ρ,hρ0⟩ (push K hM) :=
  ⟨by exact_mod_cast hρ1,push_lipschitz K hM hρ0 hK⟩

theorem exists_unique_invariant (K : Kernel Y Y) [IsMarkovKernel K] (y₀ : Y)
    (hM : PreservesFirstMoment K y₀) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : IsW1Contraction K ρ) :
    ∃! π : FirstMomentProbability y₀, Kernel.Invariant K π.measure := by
  letI : Nonempty (FirstMomentProbability y₀) := ⟨anchor y₀⟩
  have hc := push_contracting K hM hρ0 hρ1 hK
  refine ⟨hc.fixedPoint (push K hM),?_,?_⟩
  · exact congrArg FirstMomentProbability.measure hc.fixedPoint_isFixedPt
  · intro ν hν
    apply hc.fixedPoint_unique
    apply FirstMomentProbability.ext
    exact hν

noncomputable def stationary (K : Kernel Y Y) [IsMarkovKernel K] (y₀ : Y)
    (hM : PreservesFirstMoment K y₀) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : IsW1Contraction K ρ) : FirstMomentProbability y₀ :=
  Classical.choose (exists_unique_invariant K y₀ hM hρ0 hρ1 hK)

theorem stationary_invariant (K : Kernel Y Y) [IsMarkovKernel K] (y₀ : Y)
    (hM : PreservesFirstMoment K y₀) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : IsW1Contraction K ρ) :
    Kernel.Invariant K (stationary K y₀ hM hρ0 hρ1 hK).measure :=
  (Classical.choose_spec (exists_unique_invariant K y₀ hM hρ0 hρ1 hK)).1

theorem invariant_geometric_bound (K : Kernel Y Y) [IsMarkovKernel K] {y₀ : Y}
    (hM : PreservesFirstMoment K y₀) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hK : IsW1Contraction K ρ) (μ π : FirstMomentProbability y₀)
    (hπ : Kernel.Invariant K π.measure) (n : ℕ) :
    dist ((push K hM)^[n] μ) π ≤ ρ^n * dist μ π := by
  have hf : IsFixedPt (push K hM) π := FirstMomentProbability.ext hπ
  have h := ((push_lipschitz K hM hρ0 hK).iterate n).dist_le_mul μ π
  rw [(hf.iterate n).eq] at h
  simpa only [NNReal.coe_pow,NNReal.coe_mk] using! h

theorem actual_iterate_coupling_bound (K : Kernel Y Y) [IsMarkovKernel K] {y₀ : Y}
    (hM : PreservesFirstMoment K y₀) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hK : IsW1Contraction K ρ) (μ π : FirstMomentProbability y₀)
    (hπ : Kernel.Invariant K π.measure) (n : ℕ) :
    couplingW1 (iterateLaw K μ.measure n) π.measure ≤
      ρ^n * couplingW1 μ.measure π.measure := by
  have h := invariant_geometric_bound K hM hρ0 hK μ π hπ n
  change couplingW1 ((push K hM)^[n] μ).measure π.measure ≤ _ at h
  rwa [iterate_push_measure] at h

theorem iterate_tendsto_invariant (K : Kernel Y Y) [IsMarkovKernel K] {y₀ : Y}
    (hM : PreservesFirstMoment K y₀) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : IsW1Contraction K ρ) (μ π : FirstMomentProbability y₀)
    (hπ : Kernel.Invariant K π.measure) :
    Tendsto (fun n => (push K hM)^[n] μ) atTop (𝓝 π) := by
  apply tendsto_iff_dist_tendsto_zero.2
  apply squeeze_zero (fun _ => dist_nonneg)
    (invariant_geometric_bound K hM hρ0 hK μ π hπ)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (dist μ π)

theorem automatic_invariant_and_convergence (K : Kernel Y Y) [IsMarkovKernel K] (y₀ : Y)
    (hM : PreservesFirstMoment K y₀) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : IsW1Contraction K ρ) :
    ∃ π : FirstMomentProbability y₀,
      Kernel.Invariant K π.measure ∧
      (∀ ν : FirstMomentProbability y₀, Kernel.Invariant K ν.measure → ν = π) ∧
      (∀ (μ : FirstMomentProbability y₀) (n : ℕ),
        couplingW1 (iterateLaw K μ.measure n) π.measure ≤
          ρ^n * couplingW1 μ.measure π.measure) ∧
      (∀ μ : FirstMomentProbability y₀,
        Tendsto (fun n => (push K hM)^[n] μ) atTop (𝓝 π)) := by
  obtain ⟨π,hπ,huniq⟩ := exists_unique_invariant K y₀ hM hρ0 hρ1 hK
  exact ⟨π,hπ,huniq,fun μ n => actual_iterate_coupling_bound K hM hρ0 hK μ π hπ n,
    fun μ => iterate_tendsto_invariant K hM hρ0 hρ1 hK μ π hπ⟩

end PermanssonResearch.Perturbation.FirstMomentInvariant
