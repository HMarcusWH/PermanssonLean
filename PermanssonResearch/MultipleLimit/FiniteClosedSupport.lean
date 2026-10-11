import PermanssonResearch.MultipleLimit.FiniteCesaroAlgebra
import Mathlib.Tactic

/-!
# Lane C2 — exact preservation of support by closed finite stochastic blocks

A real transition matrix that has no edges from a frozen closed subset
to its complement preserves support of every row vector contained in
that subset. This is proved for all finite powers and Cesaro averages.

The result is independent of stationarity, irreducibility or rational
weights. It will let us construct the stationary distribution of EACH
closed recurrent class by taking Cesaro limits starting within it.

No class invariant existence or a.s. occupation conclusion is smuggled
into these lemmas.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteClosedSupport

open FiniteCesaroAlgebra

variable {Y : Type*} [Fintype Y]

/-- Algebraic graph closure for a transition matrix: every excluded
one-step destination has exactly zero mass. -/
def IsClosedReal (K : Y → Y → ℝ) (C : Set Y) : Prop :=
  ∀ i ∈ C, ∀ j ∉ C, K i j = 0

/-- Statewise support of a real row vector on C. -/
def IsSupportedReal (v : Y → ℝ) (C : Set Y) : Prop :=
  ∀ j ∉ C, v j = 0

theorem pushVector_support
    (K : Y → Y → ℝ) (C : Set Y) (hC : IsClosedReal K C)
    (v : Y → ℝ) (hv : IsSupportedReal v C) :
    IsSupportedReal (pushVector K v) C := by
  intro j hj
  unfold pushVector
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hiC : i ∈ C
  · rw [hC i hiC j hj, mul_zero]
  · rw [hv i hiC, zero_mul]

theorem iteratedVector_support
    (K : Y → Y → ℝ) (C : Set Y) (hC : IsClosedReal K C)
    (v : Y → ℝ) (hv : IsSupportedReal v C) :
    ∀ n, IsSupportedReal (iteratedVector K v n) C := by
  intro n
  induction n with
  | zero => exact hv
  | succ n ih =>
      exact pushVector_support K C hC _ ih

theorem orbitSum_support
    (K : Y → Y → ℝ) (C : Set Y) (hC : IsClosedReal K C)
    (v : Y → ℝ) (hv : IsSupportedReal v C) (N : ℕ) :
    IsSupportedReal (orbitSum K v N) C := by
  intro j hj
  unfold orbitSum
  apply Finset.sum_eq_zero
  intro n hn
  exact iteratedVector_support K C hC v hv n j hj

/-- All positive-horizon Cesaro averages have ZERO probability
outside the same frozen graph-closed class as the initial vector. -/
theorem cesaroVector_support
    (K : Y → Y → ℝ) (C : Set Y) (hC : IsClosedReal K C)
    (v : Y → ℝ) (hv : IsSupportedReal v C) (n : ℕ) :
    IsSupportedReal (cesaroVector K v n) C := by
  intro j hj
  unfold cesaroVector
  rw [orbitSum_support K C hC v hv (n+1) j hj, mul_zero]

end FiniteClosedSupport
end MultipleLimit
end PermanssonResearch
