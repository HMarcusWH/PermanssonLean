import PermanssonResearch.MultipleLimit.FiniteCesaroAlgebra
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Lane C2 — existence of a stationary finite REAL stochastic vector

The arbitrary real (possibly irrational) row-stochastic matrix possesses
a nonnegative probability row vector fixed by one-step pushVector.
There is NO assumption of an invariant distribution, aperiodicity
or irreducibility.

The proof takes exact Cesaro averages from a Dirac start, keeps them
inside the compact finite cube [0,1]^Y, extracts a convergent subsequence,
and uses the verified O(1/n) invariance-defect bound to prove the limit
is stationary. This is not yet the kernel-to-ENNReal representation
bridge or the irreducible class uniqueness theorem.
-/

open Filter Topology
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteInvariantExistence

open FiniteCesaroAlgebra

variable {Y : Type*} [Fintype Y] [Nonempty Y]

theorem cesaro_nonneg (K : Y → Y → ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (v : Y → ℝ) (hv : ∀ i, 0 ≤ v i)
    (n : ℕ) (j : Y) :
    0 ≤ cesaroVector K v n j := by
  unfold cesaroVector orbitSum
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro t ht
  exact iteratedVector_nonneg K hK v hv t j

theorem cesaro_total (K : Y → Y → ℝ)
    (hrow : ∀ i, ∑ j : Y, K i j = 1)
    (v : Y → ℝ) (hvtotal : (∑ i : Y, v i) = 1)
    (n : ℕ) :
    (∑ j : Y, cesaroVector K v n j) = 1 := by
  have hswap :
      (∑ j : Y, orbitSum K v (n+1) j) =
        ∑ t ∈ Finset.range (n+1), ∑ j : Y, iteratedVector K v t j := by
    simp only [orbitSum]
    exact Finset.sum_comm
  calc
    (∑ j : Y, cesaroVector K v n j) =
        (((n+1 : ℕ) : ℝ)⁻¹) * ∑ j : Y, orbitSum K v (n+1) j := by
      simp only [cesaroVector, Finset.mul_sum]
    _ = (((n+1 : ℕ) : ℝ)⁻¹) *
        (∑ t ∈ Finset.range (n+1),
          ∑ j : Y, iteratedVector K v t j) := by rw [hswap]
    _ = (((n+1 : ℕ) : ℝ)⁻¹) * (((n+1 : ℕ) : ℝ)) := by
      simp_rw [iteratedVector_mass K hrow v, hvtotal]
      simp
    _ = 1 := inv_mul_cancel₀ (by positivity)

theorem cesaro_le_one (K : Y → Y → ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (hrow : ∀ i, ∑ j : Y, K i j = 1)
    (v : Y → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hvtotal : (∑ i : Y, v i) = 1)
    (n : ℕ) (j : Y) :
    cesaroVector K v n j ≤ 1 := by
  calc
    cesaroVector K v n j ≤
        (∑ i : Y, cesaroVector K v n i) :=
      Finset.single_le_sum
        (fun i hi => cesaro_nonneg K hK v hv n i)
        (Finset.mem_univ j)
    _ = 1 := cesaro_total K hrow v hvtotal n

theorem cesaro_defect_tendsto_zero
    (K : Y → Y → ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (hrow : ∀ i, ∑ j : Y, K i j = 1)
    (v : Y → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hvtotal : (∑ i : Y, v i) = 1)
    (j : Y) :
    Tendsto
      (fun n : ℕ => pushVector K (cesaroVector K v n) j -
        cesaroVector K v n j)
      atTop (𝓝 0) := by
  have hbound (n : ℕ) :
      ‖pushVector K (cesaroVector K v n) j - cesaroVector K v n j‖ ≤
        (((n+1 : ℕ) : ℝ)⁻¹) * 2 := by
    simpa only [Real.norm_eq_abs] using
      (cesaro_probability_defect_bound K hK hrow v hv hvtotal n j)
  have hlim :
      Tendsto (fun n : ℕ => (((n+1 : ℕ) : ℝ)⁻¹) * 2)
        atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n+1 : ℕ) : ℝ))
        atTop (𝓝 0) :=
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 1)
    simpa only [one_div, zero_mul] using h0.mul_const (2 : ℝ)
  exact squeeze_zero_norm hbound hlim

/-- Existence of a stationary distribution for a finite nonempty
REAL row-stochastic transition matrix. In particular periodic chains
are supported and no stationary vector is postulated as input. -/
theorem exists_stationary_real
    (K : Y → Y → ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (hrow : ∀ i, ∑ j : Y, K i j = 1) :
    ∃ π : Y → ℝ,
      (∀ j, 0 ≤ π j) ∧
      (∑ j : Y, π j) = 1 ∧
      ∀ j, pushVector K π j = π j := by
  classical
  let y0 : Y := Classical.choice inferInstance
  let v : Y → ℝ := fun j => if j = y0 then 1 else 0
  have hv : ∀ j, 0 ≤ v j := by
    intro j
    simp [v]
  have hvtotal : (∑ j : Y, v j) = 1 := by
    simp [v]
  let u : ℕ → (Y → Set.Icc (0 : ℝ) 1) :=
    fun n j => ⟨cesaroVector K v n j, ⟨
      cesaro_nonneg K hK v hv n j,
      cesaro_le_one K hK hrow v hv hvtotal n j⟩⟩
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq u
  let π : Y → ℝ := fun j => (a j).val
  have hcoord (j : Y) :
      Tendsto (fun n : ℕ => cesaroVector K v (φ n) j)
        atTop (𝓝 (π j)) := by
    have hj : Tendsto (fun n : ℕ => u (φ n) j)
        atTop (𝓝 (a j)) :=
      (tendsto_pi_nhds.mp hlim) j
    have hj' := (continuous_subtype_val.tendsto (a j)).comp hj
    simpa only [u, π] using hj'
  have hπnonneg : ∀ j, 0 ≤ π j := by
    intro j
    exact (a j).property.1
  have hπtotal : (∑ j : Y, π j) = 1 := by
    have ht : Tendsto
        (fun n : ℕ => ∑ j : Y, cesaroVector K v (φ n) j)
        atTop (𝓝 (∑ j : Y, π j)) :=
      tendsto_finsetSum _ (fun j hj => hcoord j)
    have heq : (fun n : ℕ => ∑ j : Y, cesaroVector K v (φ n) j) =
        (fun _ : ℕ => (1 : ℝ)) := by
      funext n
      exact cesaro_total K hrow v hvtotal (φ n)
    rw [heq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hπstationary : ∀ j, pushVector K π j = π j := by
    intro j
    have hpush : Tendsto
        (fun n : ℕ => pushVector K (cesaroVector K v (φ n)) j)
        atTop (𝓝 (pushVector K π j)) := by
      unfold pushVector
      exact tendsto_finsetSum _ (fun i hi =>
        (hcoord i).mul tendsto_const_nhds)
    have hzero := (cesaro_defect_tendsto_zero K hK hrow v hv hvtotal j).comp
      hφ.tendsto_atTop
    have hsub := hpush.sub (hcoord j)
    have hEq :
        pushVector K π j - π j = 0 :=
      tendsto_nhds_unique hsub hzero
    exact sub_eq_zero.mp hEq
  exact ⟨π, hπnonneg, hπtotal, hπstationary⟩

end FiniteInvariantExistence
end MultipleLimit
end PermanssonResearch
