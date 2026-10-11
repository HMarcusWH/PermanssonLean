import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Lane C2 — finite real-vector Cesàro invariance algebra

Before invoking compactness to CONSTRUCT an invariant probability,
prove the exact telescoping identity for ordinary finite real-valued
transition matrices. The proof is purely finite algebra and makes no
stationarity, irreducibility or aperiodicity assumption.

The key exact equality is
  P * Cesaro_N(v) - Cesaro_N(v) =
    (P^(N+1) v - v)/(N+1).
This module establishes it at every physical state, not just
an expectation-level assertion.

The bridge from a general ENNReal Markov kernel to real stochastic
vectors, the compactness stationary-existence proof, and the
martingale occupation theorem are separate open obligations.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteCesaroAlgebra

variable {Y : Type*} [Fintype Y]

/-- Push a real-valued row vector through a finite transition array. -/
def pushVector (K : Y → Y → ℝ) (v : Y → ℝ) (j : Y) : ℝ :=
  ∑ i : Y, v i * K i j

/-- Real transition powers applied to an initial vector. -/
def iteratedVector (K : Y → Y → ℝ) (v : Y → ℝ) :
    ℕ → Y → ℝ
  | 0 => v
  | n + 1 => pushVector K (iteratedVector K v n)

/-- Unnormalized finite sum of all time-indexed vector iterates
at horizons 0,...,N-1. -/
def orbitSum (K : Y → Y → ℝ) (v : Y → ℝ) (N : ℕ) (j : Y) : ℝ :=
  ∑ t ∈ Finset.range N, iteratedVector K v t j

/-- Positive-horizon Cesaro average; the denominator is n+1,
with the time-zero state INCLUDED. -/
def cesaroVector (K : Y → Y → ℝ) (v : Y → ℝ) (n : ℕ) (j : Y) : ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹ * orbitSum K v (n+1) j

theorem pushVector_smul
    (K : Y → Y → ℝ) (a : ℝ) (v : Y → ℝ) (j : Y) :
    pushVector K (fun i => a * v i) j = a * pushVector K v j := by
  unfold pushVector
  simp_rw [mul_assoc]
  rw [Finset.mul_sum]

/-- Finite sums commute exactly with pushing through a fixed real kernel. -/
theorem pushVector_orbitSum
    (K : Y → Y → ℝ) (v : Y → ℝ) (N : ℕ) (j : Y) :
    pushVector K (orbitSum K v N) j =
      ∑ t ∈ Finset.range N, pushVector K (iteratedVector K v t) j := by
  calc
    pushVector K (orbitSum K v N) j =
        ∑ i : Y, ∑ t ∈ Finset.range N,
          iteratedVector K v t i * K i j := by
      simp only [pushVector, orbitSum, Finset.sum_mul]
    _ = ∑ t ∈ Finset.range N, ∑ i : Y,
          iteratedVector K v t i * K i j := Finset.sum_comm
    _ = ∑ t ∈ Finset.range N,
          pushVector K (iteratedVector K v t) j := rfl

/-- Exact finite telescoping of the Markov sequence at every coordinate.
No limiting operator or invariant law appears as an assumption. -/
theorem orbitSum_invariance_defect
    (K : Y → Y → ℝ) (v : Y → ℝ) (N : ℕ) (j : Y) :
    pushVector K (orbitSum K v N) j - orbitSum K v N j =
      iteratedVector K v N j - v j := by
  rw [pushVector_orbitSum]
  change (∑ t ∈ Finset.range N, iteratedVector K v (t+1) j) -
      (∑ t ∈ Finset.range N, iteratedVector K v t j) = _
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_range_sub (fun t => iteratedVector K v t j) N

/-- The exact Cesaro defect identity is valid for EVERY finite real
transition array and EVERY initial row vector. -/
theorem cesaro_invariance_defect
    (K : Y → Y → ℝ) (v : Y → ℝ) (n : ℕ) (j : Y) :
    pushVector K (cesaroVector K v n) j - cesaroVector K v n j =
      (((n+1 : ℕ) : ℝ)⁻¹) *
        (iteratedVector K v (n+1) j - v j) := by
  rw [show pushVector K (cesaroVector K v n) j =
      (((n+1 : ℕ) : ℝ)⁻¹) *
        pushVector K (orbitSum K v (n+1)) j from
    pushVector_smul K _ _ j]
  change (((n+1 : ℕ) : ℝ)⁻¹) *
      pushVector K (orbitSum K v (n+1)) j -
      (((n+1 : ℕ) : ℝ)⁻¹) *
        orbitSum K v (n+1) j = _
  rw [← mul_sub, orbitSum_invariance_defect]

/-- Row stochasticity preserves total mass of a finite real vector. -/
theorem pushVector_total
    (K : Y → Y → ℝ)
    (hrow : ∀ i : Y, ∑ j : Y, K i j = 1)
    (v : Y → ℝ) :
    (∑ j : Y, pushVector K v j) = ∑ i : Y, v i := by
  calc
    (∑ j : Y, pushVector K v j) =
        ∑ j : Y, ∑ i : Y, v i * K i j := rfl
    _ = ∑ i : Y, ∑ j : Y, v i * K i j := Finset.sum_comm
    _ = ∑ i : Y, v i := by
      simp_rw [← Finset.mul_sum, hrow, mul_one]

/-- Nonnegative row vectors remain nonnegative after pushing through
a nonnegative finite transition array. -/
theorem pushVector_nonneg
    (K : Y → Y → ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (v : Y → ℝ) (hv : ∀ i, 0 ≤ v i)
    (j : Y) :
    0 ≤ pushVector K v j := by
  unfold pushVector
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hv i) (hK i j)

/-- Bounded iterates force a quantitative O(1/n) residual at every
coordinate. This does not yet assume or select a cluster point. -/
theorem cesaro_invariance_defect_bound
    (K : Y → Y → ℝ) (v : Y → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbounded : ∀ n j, |iteratedVector K v n j| ≤ C)
    (n : ℕ) (j : Y) :
    |pushVector K (cesaroVector K v n) j -
      cesaroVector K v n j| ≤
        (((n+1 : ℕ) : ℝ)⁻¹) * (C + |v j|) := by
  rw [cesaro_invariance_defect, abs_mul]
  have hp : 0 ≤ (((n+1 : ℕ) : ℝ)⁻¹) := by positivity
  rw [abs_of_nonneg hp]
  apply mul_le_mul_of_nonneg_left ?_ hp
  exact (abs_sub _ _).trans ((add_le_add_right (hbounded (n+1) j) _))


/-- Nonnegative stochastic transition matrices keep iterated vectors
nonnegative, for every (possibly periodic) transition array. -/
theorem iteratedVector_nonneg
    (K : Y → Y → ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (v : Y → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∀ n j, 0 ≤ iteratedVector K v n j := by
  intro n
  induction n with
  | zero => exact hv
  | succ n ih =>
      intro j
      exact pushVector_nonneg K hK _ ih j

/-- Every real stochastic transition preserves the TOTAL MASS of all
iterated vectors, including periodic and reducible kernels. -/
theorem iteratedVector_mass
    (K : Y → Y → ℝ)
    (hrow : ∀ i : Y, ∑ j : Y, K i j = 1)
    (v : Y → ℝ) :
    ∀ n, (∑ j : Y, iteratedVector K v n j) = ∑ j : Y, v j := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (pushVector_total K hrow _).trans ih

/-- All iterated masses lie in [0,1] if the input is a genuine
real-valued probability vector. -/
theorem iteratedVector_le_one
    (K : Y → Y → ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (hrow : ∀ i : Y, ∑ j : Y, K i j = 1)
    (v : Y → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hvtotal : (∑ i : Y, v i) = 1)
    (n : ℕ) (j : Y) :
    iteratedVector K v n j ≤ 1 := by
  have hpos := iteratedVector_nonneg K hK v hv n
  calc
    iteratedVector K v n j ≤
        ∑ i : Y, iteratedVector K v n i :=
      Finset.single_le_sum (fun i hi => hpos i) (Finset.mem_univ j)
    _ = 1 := (iteratedVector_mass K hrow v n).trans hvtotal

/-- Explicit quantitative stationary defect of finite Cesaro
averages: at most 2/(n+1) at every coordinate, even when the
individual one-step marginals oscillate periodically. -/
theorem cesaro_probability_defect_bound
    (K : Y → Y → ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (hrow : ∀ i : Y, ∑ j : Y, K i j = 1)
    (v : Y → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hvtotal : (∑ i : Y, v i) = 1)
    (n : ℕ) (j : Y) :
    |pushVector K (cesaroVector K v n) j -
      cesaroVector K v n j| ≤
        (((n+1 : ℕ) : ℝ)⁻¹) * 2 := by
  have hnonneg := iteratedVector_nonneg K hK v hv
  have hbdd : ∀ t i, |iteratedVector K v t i| ≤ (1 : ℝ) := by
    intro t i
    rw [abs_of_nonneg (hnonneg t i)]
    exact iteratedVector_le_one K hK hrow v hv hvtotal t i
  have h0 : |v j| ≤ (1 : ℝ) := by
    simpa only [iteratedVector] using hbdd 0 j
  calc
    |pushVector K (cesaroVector K v n) j -
      cesaroVector K v n j| ≤
        (((n+1 : ℕ) : ℝ)⁻¹) * (1 + |v j|) :=
      cesaro_invariance_defect_bound K v 1 (by positivity) hbdd n j
    _ ≤ (((n+1 : ℕ) : ℝ)⁻¹) * 2 := by
      gcongr
      linarith


end FiniteCesaroAlgebra
end MultipleLimit
end PermanssonResearch
