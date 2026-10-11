import PermanssonResearch.MultipleLimit.FiniteClassInvariantUniqueness
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Lane C2 — deterministic compactness/uniqueness occupation limit bridge

For a nonempty finite real stochastic chain with a specified irreducible
closed class C and a proved unique class-supported invariant probability π,
ANY sequence of empirical probability VECTORS converges to π provided:
  (i) its mass outside C tends to zero in every coordinate, and
  (ii) its stationarity residual K * v_n - v_n tends to zero.

This is a genuine convergence theorem, proved from finite compactness,
subsequence extraction, and independently established class uniqueness.
It does not assume that empirical measures already converge.

The separate canonical martingale SLLN must PROVE (ii) for the real
infinite path law. Eventual class residence proves (i) for true
empirical occupations. Therefore the theorem's analytic hypotheses
are exposed rather than silently assumed in the C2 headline.
-/

open Filter Topology
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteOccupationLimitFromResidual

open FiniteCesaroAlgebra
open FiniteClassInvariantUniqueness
open FiniteClosedSupport

variable {Y : Type*} [Fintype Y] [Nonempty Y]

/-- An a priori simplex point has mass at most one in each coordinate. -/
private theorem coordinate_le_one (v : Y → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hsum : (∑ i : Y, v i) = 1) (j : Y) :
    v j ≤ 1 := by
  calc
    v j ≤ ∑ i : Y, v i :=
      Finset.single_le_sum (fun i hi => hv i) (Finset.mem_univ j)
    _ = 1 := hsum

/-- Asymptotic invariance and asymptotic closed-class support force
convergence to the UNIQUE class invariant law, even for periodic
classes and oscillatory one-step marginals. This is the deterministic
compactness half of the general finite-chain occupation theorem. -/
theorem tendsto_unique_stationary_of_residual
    (K : Y → Y → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (C : Set Y)
    (hcomm : ∀ i ∈ C, ∀ j ∈ C,
      FiniteInvariantUniqueness.Reachable K i j)
    (π : Y → ℝ)
    (hπnonneg : ∀ i, 0 ≤ π i)
    (hπmass : (∑ i : Y, π i) = 1)
    (hπstationary : ∀ j, pushVector K π j = π j)
    (hπsupport : IsSupportedReal π C)
    (v : ℕ → Y → ℝ)
    (hvnonneg : ∀ n i, 0 ≤ v n i)
    (hvmass : ∀ n, (∑ i : Y, v n i) = 1)
    (hresidual : ∀ j,
      Tendsto (fun n => pushVector K (v n) j - v n j)
        atTop (𝓝 0))
    (houtside : ∀ j ∉ C, Tendsto (fun n => v n j) atTop (𝓝 0)) :
    Tendsto v atTop (𝓝 π) := by
  classical
  let cube : ℕ → (Y → Set.Icc (0 : ℝ) 1) :=
    fun n j => ⟨v n j,
      ⟨hvnonneg n j, coordinate_le_one (v n) (hvnonneg n) (hvmass n) j⟩⟩
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨a, ms, hms, hsub⟩ :=
    CompactSpace.tendsto_subseq (fun n => cube (ns n))
  let aVec : Y → ℝ := fun j => (a j).val
  have htime : Tendsto (fun n : ℕ => ns (ms n)) atTop atTop :=
    hns.comp hms.tendsto_atTop
  have hcoord (j : Y) :
      Tendsto (fun n : ℕ => v (ns (ms n)) j)
        atTop (𝓝 (aVec j)) := by
    have hj : Tendsto (fun n : ℕ => cube (ns (ms n)) j)
        atTop (𝓝 (a j)) := (tendsto_pi_nhds.mp hsub) j
    have hval := (continuous_subtype_val.tendsto (a j)).comp hj
    change Tendsto (fun n : ℕ => v (ns (ms n)) j)
      atTop (𝓝 (aVec j)) at hval
    exact hval
  have haNonneg : ∀ j, 0 ≤ aVec j := fun j => (a j).property.1
  have haMass : (∑ j : Y, aVec j) = 1 := by
    have ht : Tendsto (fun n : ℕ => ∑ j : Y, v (ns (ms n)) j)
        atTop (𝓝 (∑ j : Y, aVec j)) :=
      tendsto_finsetSum _ (fun j hj => hcoord j)
    have heq : (fun n : ℕ => ∑ j : Y, v (ns (ms n)) j) =
        fun _ : ℕ => (1 : ℝ) := by
      funext n
      exact hvmass (ns (ms n))
    rw [heq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have haSupport : IsSupportedReal aVec C := by
    intro j hj
    have hz := (houtside j hj).comp htime
    exact tendsto_nhds_unique (hcoord j) hz
  have haStationary : ∀ j, pushVector K aVec j = aVec j := by
    intro j
    have hpush : Tendsto
        (fun n : ℕ => pushVector K (v (ns (ms n))) j)
        atTop (𝓝 (pushVector K aVec j)) := by
      unfold pushVector
      exact tendsto_finsetSum _ (fun i hi =>
        (hcoord i).mul tendsto_const_nhds)
    have hzero := (hresidual j).comp htime
    have hdiff : pushVector K aVec j - aVec j = 0 :=
      tendsto_nhds_unique (hpush.sub (hcoord j)) hzero
    exact sub_eq_zero.mp hdiff
  have heq : aVec = π :=
    stationary_probability_unique_on_class K hK C hcomm
      aVec π haNonneg hπnonneg haMass hπmass
      haStationary hπstationary haSupport hπsupport
  refine ⟨ms, ?_⟩
  rw [← heq]
  exact tendsto_pi_nhds.mpr hcoord

end FiniteOccupationLimitFromResidual
end MultipleLimit
end PermanssonResearch
