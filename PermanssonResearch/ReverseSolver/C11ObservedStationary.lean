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


/-- Exact native typed stationary mass on the frozen true-observation
event; the kernel, class, vector and descriptor are all bound to the
same checked numerical input. -/
theorem certified_true_mass {n : ℕ}
    (L : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) (h : Fin n → Bool) :
    (certifiedProbability L r hc).toMeasure
      {y : PermanssonLean.JointState Unit (Fin n) | h (encode y) = true} =
      ENNReal.ofReal (trueShare r h : ℝ) := by
  let S : Set (PermanssonLean.JointState Unit (Fin n)) :=
    {y | h (encode y) = true}
  let s : Finset (PermanssonLean.JointState Unit (Fin n)) :=
    Finset.univ.filter (fun y => h (encode y) = true)
  have hs : (↑s : Set (PermanssonLean.JointState Unit (Fin n))) = S := by
    ext y
    simp [s, S]
  have hsum : (∑ y ∈ s, realWeights r y) =
      (trueShare r h : ℝ) := by
    unfold s
    rw [Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_unique]
    change (∑ x : Fin n, if h x then ((r.weights x : ℚ) : ℝ) else 0) =
      ((∑ x : Fin n, if h x then r.weights x else 0 : ℚ) : ℝ)
    norm_cast
  change (vectorMeasure (realWeights r)) S =
    ENNReal.ofReal (trueShare r h : ℝ)
  calc
    (vectorMeasure (realWeights r)) S =
        ∑ y ∈ s, (vectorMeasure (realWeights r))
          ({y} : Set (PermanssonLean.JointState Unit (Fin n))) := by
      rw [← hs]
      exact (sum_measure_singleton).symm
    _ = ∑ y ∈ s, ENNReal.ofReal (realWeights r y) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact vectorMeasure_singleton (realWeights r) y
    _ = ENNReal.ofReal (∑ y ∈ s, realWeights r y) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun y hy =>
        realWeights_nonneg L r hc y)]
    _ = ENNReal.ofReal (trueShare r h : ℝ) := by
      rw [hsum]

theorem checked_observed_true_mass_eq_native {n : ℕ} [NeZero n]
    (K₀ L : RationalMarkovMatrix n)
    (r : ClassStationaryCandidate n)
    (hc : checkClassStationary L r = true) (h : Fin n → Bool) :
    ((PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw.stationaryForSet
      (rationalStrategicIntervention K₀ L).intervention.apply.inducedKernel
      (decodedClass r.classStates)).map
        (fun y : PermanssonLean.JointState Unit (Fin n) => h (encode y))).toMeasure
        ({true} : Set Bool) =
      ENNReal.ofReal (trueShare r h : ℝ) := by
  rw [← checked_stationary_eq_native K₀ L r hc]
  rw [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton true)]
  simpa only [Set.preimage, Set.mem_setOf_eq, Set.mem_singleton_iff] using
    certified_true_mass L r hc h

end C11
end ReverseSolver
end PermanssonResearch
