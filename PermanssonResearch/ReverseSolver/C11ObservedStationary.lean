import PermanssonResearch.ReverseSolver.C11TypedStationaryBridge
import PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
import Mathlib.Tactic

/-!
# C11-A — exact Boolean stationary mass, not eventual-always truth

Each checked irreducible class has positive stationary mass at every
class vertex. Consequently stationary observed-true share is 1 exactly
for all-true classes, 0 exactly for all-false classes, and strictly
between 0 and 1 exactly for mixed classes. C10's eventually-always
event is a different functional; none of these equations changes B₁.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace C11

set_option autoImplicit false
open C10
open FiniteStrategicRealization
open PermanssonResearch.MultipleLimit.FiniteInvariantMeasureTransport
open PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

def trueShare {n : ℕ} (r : ClassStationaryCandidate n)
    (h : Fin n → Bool) : ℚ :=
  ∑ x : Fin n, if h x then r.weights x else 0

def falseShare {n : ℕ} (r : ClassStationaryCandidate n)
    (h : Fin n → Bool) : ℚ :=
  ∑ x : Fin n, if h x then 0 else r.weights x

theorem trueShare_nonneg {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) (h : Fin n → Bool) :
    0 ≤ trueShare r h := by
  unfold trueShare
  apply Finset.sum_nonneg
  intro x hx
  by_cases ht : h x = true
  · simpa [ht] using checked_nonnegative L r hc x
  · simp [Bool.eq_false_iff.mpr ht]

theorem falseShare_nonneg {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) (h : Fin n → Bool) :
    0 ≤ falseShare r h := by
  unfold falseShare
  apply Finset.sum_nonneg
  intro x hx
  by_cases ht : h x = true
  · simp [ht]
  · simpa [Bool.eq_false_iff.mpr ht] using checked_nonnegative L r hc x

theorem share_partition {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) (h : Fin n → Bool) :
    trueShare r h + falseShare r h = 1 := by
  unfold trueShare falseShare
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x : Fin n,
        (if h x then r.weights x else 0) +
        (if h x then 0 else r.weights x)) =
        ∑ x : Fin n, r.weights x := by
          apply Finset.sum_congr rfl
          intro x hx
          cases hb : h x <;> simp [hb]
    _ = 1 := checked_normalized L r hc

theorem trueShare_positive_of_true {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) (h : Fin n → Bool)
    (x : Fin n) (hx : x ∈ r.classStates) (ht : h x = true) :
    0 < trueShare r h := by
  have hle : r.weights x ≤ trueShare r h := by
    unfold trueShare
    have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun y => if h y then r.weights y else 0)
      (fun y hy => by
        by_cases hb : h y = true
        · simpa [hb] using checked_nonnegative L r hc y
        · simp [Bool.eq_false_iff.mpr hb])
      (Finset.mem_univ x)
    simpa [ht] using hsingle
  exact lt_of_lt_of_le
    (checked_stationary_positive_on_class L L r hc x hx) hle

theorem falseShare_positive_of_false {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) (h : Fin n → Bool)
    (x : Fin n) (hx : x ∈ r.classStates) (ht : h x = false) :
    0 < falseShare r h := by
  have hle : r.weights x ≤ falseShare r h := by
    unfold falseShare
    have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun y => if h y then 0 else r.weights y)
      (fun y hy => by
        by_cases hb : h y = true
        · simp [hb]
        · simpa [Bool.eq_false_iff.mpr hb] using checked_nonnegative L r hc y)
      (Finset.mem_univ x)
    simpa [ht] using hsingle
  exact lt_of_lt_of_le
    (checked_stationary_positive_on_class L L r hc x hx) hle

theorem trueShare_one_of_all_true {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) (h : Fin n → Bool)
    (hall : ∀ x ∈ r.classStates, h x = true) :
    trueShare r h = 1 := by
  unfold trueShare
  calc
    (∑ x : Fin n, if h x then r.weights x else 0) =
        ∑ x : Fin n, r.weights x := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hcX : x ∈ r.classStates
      · simp [hall x hcX]
      · have hz := checked_supported L r hc x hcX
        simp [hz]
    _ = 1 := checked_normalized L r hc

theorem trueShare_zero_of_all_false {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) (h : Fin n → Bool)
    (hall : ∀ x ∈ r.classStates, h x = false) :
    trueShare r h = 0 := by
  unfold trueShare
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hcX : x ∈ r.classStates
  · simp [hall x hcX]
  · have hz := checked_supported L r hc x hcX
    simp [hz]

theorem trueShare_one_iff_all_true {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) (h : Fin n → Bool) :
    trueShare r h = 1 ↔
      ∀ x ∈ r.classStates, h x = true := by
  constructor
  · intro hone x hx
    by_cases ht : h x = true
    · exact ht
    · have hfalse : h x = false := Bool.eq_false_iff.mpr ht
      have hplus := share_partition L r hc h
      have hpos := falseShare_positive_of_false L r hc h x hx hfalse
      linarith
  · exact trueShare_one_of_all_true L r hc h

theorem trueShare_zero_iff_all_false {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) (h : Fin n → Bool) :
    trueShare r h = 0 ↔
      ∀ x ∈ r.classStates, h x = false := by
  constructor
  · intro hzero x hx
    by_cases ht : h x = false
    · exact ht
    · have htrue : h x = true := by cases hb : h x <;> simp_all
      have hpos := trueShare_positive_of_true L r hc h x hx htrue
      linarith
  · exact trueShare_zero_of_all_false L r hc h

theorem trueShare_mixed_iff {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) (h : Fin n → Bool) :
    (0 < trueShare r h ∧ trueShare r h < 1) ↔
      (∃ x ∈ r.classStates, h x = true) ∧
      (∃ x ∈ r.classStates, h x = false) := by
  constructor
  · rintro ⟨hpos, hlt⟩
    constructor
    · by_contra hn
      have hall : ∀ x ∈ r.classStates, h x = false := by
        intro x hx
        cases hh : h x with
        | false => rfl
        | true => exact False.elim (hn ⟨x, hx, hh⟩)
      have hz := trueShare_zero_of_all_false L r hc h hall
      linarith
    · by_contra hn
      have hall : ∀ x ∈ r.classStates, h x = true := by
        intro x hx
        cases hh : h x with
        | true => rfl
        | false => exact False.elim (hn ⟨x, hx, hh⟩)
      have ho := trueShare_one_of_all_true L r hc h hall
      linarith
  · rintro ⟨⟨x, hx, ht⟩, ⟨y, hy, hf⟩⟩
    have hp := trueShare_positive_of_true L r hc h x hx ht
    have hfp := falseShare_positive_of_false L r hc h y hy hf
    have hs := share_partition L r hc h
    constructor
    · exact hp
    · linarith

end C11
end ReverseSolver
end PermanssonResearch
