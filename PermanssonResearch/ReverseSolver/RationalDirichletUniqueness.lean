import PermanssonResearch.ReverseSolver.RationalTypedSupportBridge
import Mathlib.Tactic

/-!
# C10 — finite rational Dirichlet uniqueness from genuine positive-graph access

This module proves a genuine discrete maximum principle in the original exact
rational Markov rows, with no spectral assumptions or numerical cutoffs. Given
an explicit finite nonempty absorbing boundary reachable from every state,
a harmonic extension with zero boundary is zero. Thus two complete Dirichlet
solutions with the same boundary data coincide. A subsequent theorem must
prove the C10 computed BSCC union satisfies the access assumption for every
valid Markov matrix and connect the unique solution to infinite path laws.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open RationalTypedSupportBridge

/-- A strictly positive row entry propagates any attained global maximum
of a stochastic harmonic function. The proof uses each nonnegative term
in the zero sum of weighted gaps; it does not assume irreducibility. -/
theorem harmonic_max_edge {n : ℕ}
    (K : RationalMarkovMatrix n) (f : Fin n → ℚ) (m : ℚ)
    (hmax : ∀ y : Fin n, f y ≤ m)
    (x z : Fin n)
    (hx : f x = m)
    (hh : f x = ∑ y : Fin n, K.entry x y * f y)
    (hedge : 0 < K.entry x z) :
    f z = m := by
  have hsum : (∑ y : Fin n, K.entry x y * (m - f y)) = 0 := by
    calc
      (∑ y : Fin n, K.entry x y * (m - f y)) =
          (∑ y : Fin n, K.entry x y * m) -
            (∑ y : Fin n, K.entry x y * f y) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
      _ = m - f x := by
        rw [← Finset.sum_mul, K.row_sum_one x, ← hh]
        ring
      _ = 0 := by rw [hx]; ring
  apply le_antisymm (hmax z)
  by_contra hnot
  have hgap : 0 < m - f z := sub_pos.mpr (lt_of_not_ge hnot)
  have hterm : 0 < K.entry x z * (m - f z) := mul_pos hedge hgap
  have hle : K.entry x z * (m - f z) ≤
      ∑ y : Fin n, K.entry x y * (m - f y) := by
    simpa only using
      (Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun y => K.entry x y * (m - f y))
        (fun y hy => mul_nonneg (K.entry_nonneg x y)
          (sub_nonneg.mpr (hmax y)))
        (Finset.mem_univ z))
  rw [hsum] at hle
  exact (not_le_of_gt hterm) hle

/-- A positive global maximum travels along every genuinely reachable
positive-edge path until either the boundary is reached or contradiction. -/
private theorem harmonic_max_path {n : ℕ}
    (K : RationalMarkovMatrix n) (R : Finset (Fin n))
    (f : Fin n → ℚ) (m : ℚ)
    (hmax : ∀ y : Fin n, f y ≤ m)
    (hbd : ∀ y ∈ R, f y = 0)
    (hhar : ∀ y ∉ R,
      f y = ∑ z : Fin n, K.entry y z * f z)
    (hm : 0 < m)
    (x z : Fin n) (hx : f x = m)
    (hpath : RationalReachable K x z) : f z = m := by
  induction hpath with
  | refl => exact hx
  | @tail a b hab hedge ih =>
      have ha : a ∉ R := by
        intro hmem
        have hzero := hbd a hmem
        rw [hzero] at ih
        exact (ne_of_gt hm) ih.symm
      change 0 < K.entry a b at hedge
      exact harmonic_max_edge K f m hmax a b ih (hhar a ha) hedge

/-- Every finite rational stochastic chain with boundary access admits
no positive harmonic maximum when the prescribed boundary is zero. -/
private theorem harmonic_nonpositive_of_boundary_access {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (R : Finset (Fin n))
    (haccess : ∀ x : Fin n, ∃ z ∈ R, RationalReachable K x z)
    (f : Fin n → ℚ)
    (hbd : ∀ y ∈ R, f y = 0)
    (hhar : ∀ y ∉ R,
      f y = ∑ z : Fin n, K.entry y z * f z) :
    ∀ y : Fin n, f y ≤ 0 := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  obtain ⟨x, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n)) f hne
  have hglobal : ∀ y : Fin n, f y ≤ f x := by
    intro y
    exact hmax y (Finset.mem_univ y)
  have hx : f x ≤ 0 := by
    by_contra hnot
    have hp : 0 < f x := lt_of_not_ge hnot
    obtain ⟨z, hz, hreach⟩ := haccess x
    have hval := harmonic_max_path K R f (f x) hglobal hbd
      hhar hp x z rfl hreach
    have hzero := hbd z hz
    linarith
  intro y
  exact le_trans (hglobal y) hx

/-- Genuine uniqueness for a finite rational harmonic boundary problem.
The access hypothesis can later be discharged by C10's *complete* BSCC
enumerator; no stochastic irreducibility, primitive power, or q-cutoff. -/
theorem harmonic_zero_of_boundary_access {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (R : Finset (Fin n))
    (haccess : ∀ x : Fin n, ∃ z ∈ R, RationalReachable K x z)
    (f : Fin n → ℚ)
    (hbd : ∀ y ∈ R, f y = 0)
    (hhar : ∀ y ∉ R,
      f y = ∑ z : Fin n, K.entry y z * f z) :
    ∀ y : Fin n, f y = 0 := by
  have hupper := harmonic_nonpositive_of_boundary_access K R haccess f hbd hhar
  have hnegB : ∀ y ∈ R, -f y = 0 := by
    intro y hy
    rw [hbd y hy]
    ring
  have hnegH : ∀ y ∉ R,
      -f y = ∑ z : Fin n, K.entry y z * (-f z) := by
    intro y hy
    have eqn := congrArg Neg.neg (hhar y hy)
    simpa only [← mul_neg, ← Finset.sum_neg_distrib] using eqn
  have hlower := harmonic_nonpositive_of_boundary_access K R haccess
    (fun y => -f y) hnegB hnegH
  intro y
  have ha := hupper y
  have hb := hlower y

  linarith

/-- The exact rational boundary-value problem has at most one solution;
no unproved field inversion or numerical agreement is postulated. -/
theorem harmonic_solution_unique_of_boundary_access {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (R : Finset (Fin n))
    (haccess : ∀ x : Fin n, ∃ z ∈ R, RationalReachable K x z)
    (f g : Fin n → ℚ)
    (hfB : ∀ y ∈ R, f y = g y)
    (hfH : ∀ y ∉ R,
      f y = ∑ z : Fin n, K.entry y z * f z)
    (hgH : ∀ y ∉ R,
      g y = ∑ z : Fin n, K.entry y z * g z) :
    f = g := by
  have hdb : ∀ y ∈ R, f y - g y = 0 := by
    intro y hy
    rw [hfB y hy]
    ring
  have hdh : ∀ y ∉ R,
      f y - g y = ∑ z : Fin n, K.entry y z * (f z - g z) := by
    intro y hy
    rw [hfH y hy, hgH y hy]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  have hzero := harmonic_zero_of_boundary_access K R haccess
    (fun y => f y - g y) hdb hdh
  funext y
  have hy := hzero y

  linarith

end C10
end ReverseSolver
end PermanssonResearch