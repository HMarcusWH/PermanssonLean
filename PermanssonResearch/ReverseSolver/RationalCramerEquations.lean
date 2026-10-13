import PermanssonResearch.ReverseSolver.RationalDirichletDeterminant
import PermanssonResearch.ReverseSolver.RationalAbsorptionSolve
import Mathlib.Tactic

/-!
# C10 — universal exact Cramer Dirichlet boundary equations

The rational adjugate formula is now proved against the genuine computed
bottom-class boundary. These lemmas need no probabilistic identification:
Cramer's equation and full-system nonsingularity imply the correct Dirichlet
boundary values and harmonic equations at every transient state.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- Every genuine computed recurrent row has the exact target-class indicator
value under the total Cramer candidate, not merely an assumed boundary. -/
theorem cramerWeight_boundary {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (C : Finset (Fin n))
    (x : Fin n) (hx : x ∈ rationalRecurrentUnion K) :
    cramerWeight K C x = (if x ∈ C then 1 else 0) := by
  have hEq := cramerWeight_satisfies_matrix_equation K C
      (dirichletMatrix_det_ne_zero K) x
  have hrow (y : Fin n) :
      dirichletMatrix K x y = (if x = y then 1 else 0) := by
    simp [dirichletMatrix, killedTransientEntry, hx]
  have hLHS :
      (∑ y : Fin n, dirichletMatrix K x y * cramerWeight K C y) =
        cramerWeight K C x := by
    simp only [hrow]
    simp [eq_comm]
  rw [hLHS] at hEq
  simpa [dirichletRHS, hx] using hEq

/-- On a transient row, the full, genuine stochastic harmonic equation holds.
The forcing of the killed system is exactly compensated by the already
proved class-indicator boundary values. -/
theorem cramerWeight_transient_harmonic {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (C : Finset (Fin n))
    (hC : C ∈ bottomClasses K)
    (x : Fin n) (hx : x ∉ rationalRecurrentUnion K) :
    cramerWeight K C x =
      ∑ y : Fin n, K.entry x y * cramerWeight K C y := by
  let f : Fin n → ℚ := cramerWeight K C
  have hEq :
      (∑ y : Fin n, dirichletMatrix K x y * f y) =
        dirichletRHS K C x :=
    cramerWeight_satisfies_matrix_equation K C
      (dirichletMatrix_det_ne_zero K) x
  have hLHS :
      (∑ y : Fin n, dirichletMatrix K x y * f y) =
        f x - ∑ y : Fin n, killedTransientEntry K x y * f y := by
    calc
      (∑ y : Fin n, dirichletMatrix K x y * f y) =
          (∑ y : Fin n, (if x = y then (1 : ℚ) else 0) * f y) -
            (∑ y : Fin n, killedTransientEntry K x y * f y) := by
        simp_rw [dirichletMatrix, sub_mul]
        rw [Finset.sum_sub_distrib]
      _ = f x - ∑ y : Fin n, killedTransientEntry K x y * f y := by
        simp [eq_comm]
  have hTerm (y : Fin n) :
      K.entry x y * f y =
        killedTransientEntry K x y * f y +
          (if y ∈ C then K.entry x y else 0) := by
    by_cases hyR : y ∈ rationalRecurrentUnion K
    · have hf := cramerWeight_boundary K C y hyR
      change f y = (if y ∈ C then 1 else 0) at hf
      by_cases hyC : y ∈ C
      · simp [killedTransientEntry, hx, hyR, hf, hyC]
      · simp [killedTransientEntry, hx, hyR, hf, hyC]
    · have hyC : y ∉ C := by
        intro hy
        exact hyR ((Finset.mem_biUnion).mpr ⟨C, hC, hy⟩)
      simp [killedTransientEntry, hx, hyR, hyC]
  have hRHS :
      (∑ y : Fin n, K.entry x y * f y) =
        (∑ y : Fin n, killedTransientEntry K x y * f y) +
          dirichletRHS K C x := by
    calc
      (∑ y : Fin n, K.entry x y * f y) =
          (∑ y : Fin n,
            (killedTransientEntry K x y * f y +
              if y ∈ C then K.entry x y else 0)) := by
        apply Finset.sum_congr rfl
        intro y _
        exact hTerm y
      _ = (∑ y : Fin n, killedTransientEntry K x y * f y) +
            (∑ y : Fin n, if y ∈ C then K.entry x y else 0) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ y : Fin n, killedTransientEntry K x y * f y) +
            dirichletRHS K C x := by
        simp [dirichletRHS, hx]
  rw [hLHS] at hEq
  rw [hRHS]
  change f x =
    (∑ y : Fin n, killedTransientEntry K x y * f y) +
      dirichletRHS K C x
  linarith

end C10
end ReverseSolver
end PermanssonResearch