import PermanssonResearch.ReverseSolver.RationalCramerBounds
import PermanssonResearch.ReverseSolver.RationalCramerEquations
import PermanssonResearch.ReverseSolver.RationalRecurrentAccess
import PermanssonResearch.ReverseSolver.RationalKernel
import Mathlib.Tactic

/-!
# C10 — finite stopped-hitting envelopes for true class absorption

The rational Cramer candidate is compared at EVERY finite horizon with
D0's original exact rational target-before-forbidden recurrence, taking
C as the goal and the other recurrent states as forbidden. Their difference
is between zero and the probability of having avoided the complete
recurrent union. This is the algebraic precursor to proving equality
with genuine infinite-path absorption probabilities via a.s. recurrent entry.
It does not, by itself, assert that limiting equality.
-/
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- The physical class is the goal; other recurrent states are forbidden. -/
def classFirstTarget {n : ℕ} (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) : RationalHittingTarget n where
  goal := C
  forbidden := rationalRecurrentUnion K \ C
  disjoint := by
    apply Finset.disjoint_left.mpr
    intro x hx hg
    exact (Finset.mem_sdiff.mp hg).2 hx

/-- Rational finite-horizon probability of entering C before another
recurrent class; equivalent to D0's frozen target-before-forbidden. -/
def stoppedClassHit {n : ℕ} (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) : ℕ → Fin n → ℚ
  | 0, x => if x ∈ C then 1 else 0
  | T+1, x =>
      if x ∈ C then 1
      else if x ∈ rationalRecurrentUnion K then 0
      else ∑ y : Fin n, K.entry x y * stoppedClassHit K C T y

/-- Exact rational survival until past the prescribed finite horizon,
with initial recurrent states already considered stopped at time zero. -/
def beforeRecurrent {n : ℕ} (K : RationalMarkovMatrix n) : ℕ → Fin n → ℚ
  | 0, x => if x ∈ rationalRecurrentUnion K then 0 else 1
  | T+1, x =>
      if x ∈ rationalRecurrentUnion K then 0
      else ∑ y : Fin n, K.entry x y * beforeRecurrent K T y

/-- Nothing is changed from D0's already proved finite hitting recursion. -/
theorem stoppedClassHit_eq_D0 {n : ℕ}
    (K : RationalMarkovMatrix n) (C : Finset (Fin n)) :
    ∀ T : ℕ, ∀ x : Fin n,
      stoppedClassHit K C T x =
        rationalHittingValue K (classFirstTarget K C) T x := by
  intro T
  induction T with
  | zero =>
      intro x
      rfl
  | succ T ih =>
      intro x
      by_cases hxC : x ∈ C
      · simp [stoppedClassHit, rationalHittingValue,
          classFirstTarget, hxC]
      · by_cases hxR : x ∈ rationalRecurrentUnion K
        · simp [stoppedClassHit, rationalHittingValue,
            classFirstTarget, hxC, hxR]
        · simp [stoppedClassHit, rationalHittingValue,
            classFirstTarget, hxC, hxR, ih]

/-- All stopped paths from an already recurrent state are resolved at
once, including every distinct class at the stated time-zero boundary. -/
theorem stoppedClassHit_recurrent {n : ℕ}
    (K : RationalMarkovMatrix n) (C : Finset (Fin n))
    (T : ℕ) (x : Fin n) (hx : x ∈ rationalRecurrentUnion K) :
    stoppedClassHit K C T x = (if x ∈ C then 1 else 0) := by
  cases T with
  | zero => rfl
  | succ T =>
      by_cases hxC : x ∈ C
      · simp [stoppedClassHit, hxC]
      · simp [stoppedClassHit, hxC, hx]

/-- Exact rational error envelope. No numerical approximation, no
mixing up max/min, and no post-hoc change of comparison states. -/
theorem stoppedClassHit_error_le_survival {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) (C : Finset (Fin n))
    (hC : C ∈ bottomClasses K) :
    ∀ T : ℕ, ∀ x : Fin n,
      0 ≤ cramerWeight K C x - stoppedClassHit K C T x ∧
      cramerWeight K C x - stoppedClassHit K C T x ≤
        beforeRecurrent K T x := by
  intro T
  induction T with
  | zero =>
      intro x
      by_cases hxR : x ∈ rationalRecurrentUnion K
      · rw [cramerWeight_boundary K C x hxR,
            stoppedClassHit_recurrent K C 0 x hxR]
        simp [beforeRecurrent, hxR]
      · have hxC : x ∉ C := by
          intro hx
          exact hxR ((Finset.mem_biUnion).mpr ⟨C, hC, hx⟩)
        have hb := cramerWeight_unit_interval K C hC x
        simp only [stoppedClassHit, if_neg hxC, beforeRecurrent,
          if_neg hxR, sub_zero]
        exact hb
  | succ T ih =>
      intro x
      by_cases hxR : x ∈ rationalRecurrentUnion K
      · rw [cramerWeight_boundary K C x hxR,
            stoppedClassHit_recurrent K C (T+1) x hxR]
        simp [beforeRecurrent, hxR]
      · have hxC : x ∉ C := by
          intro hx
          exact hxR ((Finset.mem_biUnion).mpr ⟨C, hC, hx⟩)
        have hCramer := cramerWeight_transient_harmonic K C hC x hxR
        have hStop : stoppedClassHit K C (T+1) x =
            ∑ y : Fin n, K.entry x y * stoppedClassHit K C T y := by
          simp [stoppedClassHit, hxC, hxR]
        have hSurvival : beforeRecurrent K (T+1) x =
            ∑ y : Fin n, K.entry x y * beforeRecurrent K T y := by
          simp [beforeRecurrent, hxR]
        rw [hCramer, hStop, hSurvival]
        have hDifference :
            (∑ y : Fin n, K.entry x y * cramerWeight K C y) -
                (∑ y : Fin n, K.entry x y * stoppedClassHit K C T y) =
              (∑ y : Fin n,
                K.entry x y *
                  (cramerWeight K C y - stoppedClassHit K C T y)) := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
        rw [hDifference]
        constructor
        · apply Finset.sum_nonneg
          intro y hy
          exact mul_nonneg (K.entry_nonneg x y) (ih y).1
        · apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul_of_nonneg_left (ih y).2 (K.entry_nonneg x y)

end C10
end ReverseSolver
end PermanssonResearch