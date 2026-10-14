import PermanssonResearch.ReverseSolver.RationalCramerEquations
import PermanssonResearch.ReverseSolver.RationalBSCCPartition
import PermanssonResearch.ReverseSolver.RationalRecurrentAccess
import Mathlib.Tactic

/-!
# C10 — the exact Cramer class-absorption columns sum to one

For every nonempty rational Markov matrix the sum of the Cramer solutions
over the *complete* computed bottom-class menu has indicator boundary one
and is stochastic harmonic everywhere else. The universal Dirichlet
uniqueness theorem forces that sum to be the constant one function.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- Complete rational class-column sum, no missing recurrent class. -/
def cramerTotal {n : ℕ} (K : RationalMarkovMatrix n)
    (x : Fin n) : ℚ :=
  ∑ C ∈ bottomClasses K, cramerWeight K C x

theorem cramerTotal_boundary {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n)
    (x : Fin n) (hx : x ∈ rationalRecurrentUnion K) :
    cramerTotal K x = 1 := by
  unfold cramerTotal
  calc
    (∑ C ∈ bottomClasses K, cramerWeight K C x) =
      (∑ C ∈ bottomClasses K, if x ∈ C then (1 : ℚ) else 0) := by
        apply Finset.sum_congr rfl
        intro C hC
        exact cramerWeight_boundary K C x hx
    _ = 1 := bottomClasses_indicator_sum_one K x hx

theorem cramerTotal_transient_harmonic {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n)
    (x : Fin n) (hx : x ∉ rationalRecurrentUnion K) :
    cramerTotal K x = ∑ y : Fin n, K.entry x y * cramerTotal K y := by
  unfold cramerTotal
  calc
    (∑ C ∈ bottomClasses K, cramerWeight K C x) =
      (∑ C ∈ bottomClasses K,
        ∑ y : Fin n, K.entry x y * cramerWeight K C y) := by
        apply Finset.sum_congr rfl
        intro C hC
        exact cramerWeight_transient_harmonic K C hC x hx
    _ = (∑ y : Fin n,
        ∑ C ∈ bottomClasses K, K.entry x y * cramerWeight K C y) := by
        rw [Finset.sum_comm]
    _ = (∑ y : Fin n, K.entry x y *
          (∑ C ∈ bottomClasses K, cramerWeight K C y)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum]

/-- The complete class-absorption mass of the exact Cramer solver is 1
at every state, not only at previously recurrent states. -/
theorem cramerTotal_eq_one {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (x : Fin n) :
    cramerTotal K x = 1 := by
  have hB : ∀ y ∈ rationalRecurrentUnion K,
      cramerTotal K y = (1 : ℚ) :=
    fun y hy => cramerTotal_boundary K y hy
  have hT : ∀ y ∉ rationalRecurrentUnion K,
      cramerTotal K y = ∑ z : Fin n, K.entry y z * cramerTotal K z :=
    fun y hy => cramerTotal_transient_harmonic K y hy
  have hOne : ∀ y ∉ rationalRecurrentUnion K,
      (1 : ℚ) = ∑ z : Fin n, K.entry y z * (1 : ℚ) := by
    intro y _
    simpa using (K.row_sum_one y).symm
  have hEq := rationalBSCC_dirichlet_unique K
    (cramerTotal K) (fun _ => (1 : ℚ)) hB hT hOne
  exact congrFun hEq x

end C10
end ReverseSolver
end PermanssonResearch