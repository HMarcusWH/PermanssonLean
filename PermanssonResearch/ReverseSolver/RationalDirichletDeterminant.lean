import PermanssonResearch.ReverseSolver.RationalRecurrentAccess
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

/-!
# C10 — no singular transient Dirichlet matrix for a finite Markov chain

The full-state A = I - Q has identity rows on the computed recurrent union
and only transient-to-transient K entries off the diagonal. The exact graph
access theorem and rational harmonic maximum principle imply its kernel is
trivial. Matrix.exists_mulVec_eq_zero_iff then proves det A ≠ 0 on EVERY
nonempty finite stochastic kernel. This closes the non-vacuity precondition
of the Cramer-based exact rational reference solver.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- A zero Dirichlet row output at a truly recurrent state forces the
vector's corresponding boundary coordinate to vanish. -/
private theorem zero_mulVec_boundary {n : ℕ}
    (K : RationalMarkovMatrix n) (v : Fin n → ℚ)
    (h : (dirichletMatrix K).mulVec v = 0)
    (x : Fin n) (hx : x ∈ rationalRecurrentUnion K) :
    v x = 0 := by
  have hzero := congrFun h x
  have hid : ∀ y : Fin n,
      dirichletMatrix K x y = (if x = y then 1 else 0) := by
    intro y
    simp [dirichletMatrix, killedTransientEntry, hx]
  have hpoint : (∑ y : Fin n,
      dirichletMatrix K x y * v y) = 0 := by
    simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using hzero
  simp only [hid] at hpoint
  simpa [eq_comm] using hpoint

/-- With zero boundary coordinates, a zero Dirichlet row means exactly
the genuine full row-stochastic harmonic equation at a transient state. -/
private theorem zero_mulVec_transient {n : ℕ}
    (K : RationalMarkovMatrix n) (v : Fin n → ℚ)
    (h : (dirichletMatrix K).mulVec v = 0)
    (hboundary : ∀ y ∈ rationalRecurrentUnion K, v y = 0)
    (x : Fin n) (hx : x ∉ rationalRecurrentUnion K) :
    v x = ∑ y : Fin n, K.entry x y * v y := by
  have hzero := congrFun h x
  have hpoint : (∑ y : Fin n,
      dirichletMatrix K x y * v y) = 0 := by
    simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using hzero
  have hrow : (∑ y : Fin n, dirichletMatrix K x y * v y) =
      v x - ∑ y : Fin n, K.entry x y * v y := by
    calc
      (∑ y : Fin n, dirichletMatrix K x y * v y) =
          (∑ y : Fin n, (if x = y then (1 : ℚ) else 0) * v y) -
            (∑ y : Fin n, killedTransientEntry K x y * v y) := by
        simp_rw [dirichletMatrix, sub_mul]
        rw [Finset.sum_sub_distrib]
      _ = v x - ∑ y : Fin n, K.entry x y * v y := by
        have hdiag : (∑ y : Fin n, (if x = y then (1 : ℚ) else 0) * v y) =
            v x := by simp [eq_comm]
        have hrest : (∑ y : Fin n, killedTransientEntry K x y * v y) =
            ∑ y : Fin n, K.entry x y * v y := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hyR : y ∈ rationalRecurrentUnion K
          · simp [killedTransientEntry, hx, hyR, hboundary y hyR]
          · simp [killedTransientEntry, hx, hyR]
        rw [hdiag, hrest]
  rw [hrow] at hpoint
  linarith

/-- Unlike the full matrix I-K, I-Q for the killed transient system
is nonsingular for every valid finite stochastic input. -/
theorem dirichletMatrix_det_ne_zero {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) :
    (dirichletMatrix K).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hvnonzero, hkernel⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  have hB : ∀ x ∈ rationalRecurrentUnion K, v x = 0 :=
    zero_mulVec_boundary K v hkernel
  have hT : ∀ x ∉ rationalRecurrentUnion K,
      v x = ∑ y : Fin n, K.entry x y * v y :=
    zero_mulVec_transient K v hkernel hB
  have hall := harmonic_zero_of_boundary_access K
    (rationalRecurrentUnion K)
    (every_state_reaches_rational_recurrent K) v hB hT
  have hvzero : v = 0 := by
    funext x
    exact hall x
  exact hvnonzero hvzero

end C10
end ReverseSolver
end PermanssonResearch