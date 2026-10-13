import PermanssonResearch.ReverseSolver.RationalDirichletUniqueness
import Mathlib.Tactic

/-!
# C10 — finite rational maximum principle with bounded boundary values

The original C10 uniqueness proof covers a zero boundary. The same exact
stochastic maximum principle also bounds any harmonic extension between
the minimum and maximum imposed by a reachable boundary. This supplies
non-vacuous class-absorption bounds for Cramer's exact rational solution.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- A rational harmonic function can never exceed a constant upper
boundary value when every finite state can reach the boundary. -/
theorem harmonic_upper_bound {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (R : Finset (Fin n))
    (haccess : ∀ x : Fin n, ∃ z ∈ R,
      RationalTypedSupportBridge.RationalReachable K x z)
    (f : Fin n → ℚ) (m : ℚ)
    (hbd : ∀ y ∈ R, f y ≤ m)
    (hhar : ∀ y ∉ R,
      f y = ∑ z : Fin n, K.entry y z * f z) :
    ∀ y : Fin n, f y ≤ m := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty
  obtain ⟨x, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n)) f hne
  have hglobal : ∀ y : Fin n, f y ≤ f x := by
    intro y
    exact hmax y (Finset.mem_univ y)
  by_cases hmx : f x ≤ m
  · intro y
    exact (hglobal y).trans hmx
  · have hgt : m < f x := lt_of_not_ge hmx
    have hpath_bound : ∀ (a b : Fin n), f a = f x →
        RationalTypedSupportBridge.RationalReachable K a b → f b = f x := by
      intro a b ha hp
      induction hp with
      | refl => exact ha
      | @tail c d hcd hedge ih =>
          have hc : c ∉ R := by
            intro hr
            have hb := hbd c hr
            rw [ih] at hb
            exact (not_le_of_gt hgt) hb
          change 0 < K.entry c d at hedge
          exact harmonic_max_edge K f (f x) hglobal
            c d ih (hhar c hc) hedge
    obtain ⟨z, hz, hp⟩ := haccess x
    have hval := hpath_bound x z rfl hp
    have hb := hbd z hz
    rw [hval] at hb
    exact False.elim ((not_le_of_gt hgt) hb)

/-- Harmonic solutions whose boundary data lie in [0,1] remain in
[0,1] on the entire finite Markov chain. -/
theorem harmonic_unit_interval {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (R : Finset (Fin n))
    (haccess : ∀ x : Fin n, ∃ z ∈ R,
      RationalTypedSupportBridge.RationalReachable K x z)
    (f : Fin n → ℚ)
    (hbd : ∀ y ∈ R, 0 ≤ f y ∧ f y ≤ 1)
    (hhar : ∀ y ∉ R,
      f y = ∑ z : Fin n, K.entry y z * f z) :
    ∀ y : Fin n, 0 ≤ f y ∧ f y ≤ 1 := by
  have hUpper := harmonic_upper_bound K R haccess f 1
    (fun y hy => (hbd y hy).2) hhar
  have hNegBoundary : ∀ y ∈ R, -f y ≤ 0 := by
    intro y hy
    linarith [(hbd y hy).1]
  have hNegHarmonic : ∀ y ∉ R,
      -f y = ∑ z : Fin n, K.entry y z * (-f z) := by
    intro y hy
    have eqn := congrArg Neg.neg (hhar y hy)
    simpa only [← mul_neg, ← Finset.sum_neg_distrib] using eqn
  have hLower := harmonic_upper_bound K R haccess
    (fun y => -f y) 0 hNegBoundary hNegHarmonic
  intro y
  have ha := hLower y
  have hb := hUpper y
  exact ⟨by dsimp at ha; linarith, hb⟩

end C10
end ReverseSolver
end PermanssonResearch