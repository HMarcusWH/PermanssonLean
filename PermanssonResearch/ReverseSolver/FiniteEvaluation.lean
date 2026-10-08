import PermanssonResearch.ReverseSolver.RationalKernel
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# D0-B: exact weighted finite-path enumeration

Independent of the backwards recursion, these functions enumerate every
length-T successor word and multiply the corresponding rational transition
probabilities. This is a concrete, nonadaptive finite-state *forward*
semantics; proving that it equals the mathlib canonical finitePrefixLaw for
a particular kernel remains a separate measure-theoretic obligation.
-/

namespace PermanssonResearch
namespace ReverseSolver

/-- Enumerate all successor words of length T (time zero is the input state). -/
def finiteSuccessorWords (n : ℕ) : ℕ → List (List (Fin n))
  | 0 => [[]]
  | t + 1 =>
      (List.finRange n).flatMap fun z =>
        (finiteSuccessorWords n t).map (List.cons z)

/-- Product of one-step probabilities along an explicitly listed successor word. -/
def successorWordMass {n : ℕ} (K : RationalMarkovMatrix n)
    (y : Fin n) : List (Fin n) → ℚ
  | [] => 1
  | z :: zs => K.entry y z * successorWordMass K z zs

/-- The event on a successor word: reach goal at time 0..T without
previously visiting forbidden. Later visits do not undo an earlier goal. -/
def successorWordWins {n : ℕ} (target : RationalHittingTarget n)
    (y : Fin n) : List (Fin n) → Bool
  | [] => decide (y ∈ target.goal)
  | z :: zs =>
      if y ∈ target.goal then true
      else if y ∈ target.forbidden then false
      else successorWordWins target z zs

/-- Sum of weights of the successful complete words. -/
def rationalForwardEnumeration {n : ℕ} (K : RationalMarkovMatrix n)
    (target : RationalHittingTarget n) (T : ℕ) (y : Fin n) : ℚ :=
  ((finiteSuccessorWords n T).map fun xs =>
    successorWordMass K y xs *
      (if successorWordWins target y xs then (1 : ℚ) else 0)).sum

private theorem sum_map_flatMap {α β : Type*}
    (xs : List α) (f : α → List β) (g : β → ℚ) :
    ((xs.flatMap f).map g).sum =
      (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

private theorem sum_map_finRange (n : ℕ) (g : Fin n → ℚ) :
    ((List.finRange n).map g).sum = ∑ z : Fin n, g z := by
  rw [← List.sum_toFinset g (List.nodup_finRange n)]
  simp

/-- For each initial state and horizon the complete list of successor
words has total exact rational mass one. -/
theorem successorWordMass_total {n : ℕ} (K : RationalMarkovMatrix n) :
    ∀ (T : ℕ) (y : Fin n),
      ((finiteSuccessorWords n T).map (successorWordMass K y)).sum = 1 := by
  intro T
  induction T with
  | zero =>
      intro y
      simp [finiteSuccessorWords, successorWordMass]
  | succ T ih =>
      intro y
      calc
        ((finiteSuccessorWords n (T+1)).map (successorWordMass K y)).sum =
          ((List.finRange n).map (fun z =>
              ((finiteSuccessorWords n T).map
                (fun xs => K.entry y z * successorWordMass K z xs)).sum)).sum := by
            simp [finiteSuccessorWords, sum_map_flatMap, List.map_map,
              Function.comp_def, successorWordMass]
        _ = ((List.finRange n).map (fun z => K.entry y z)).sum := by
            simp [List.sum_map_mul_left, ih]
        _ = 1 := by rw [sum_map_finRange, K.row_sum_one]

private theorem finiteSuccessorWords_succ_nonempty {n : ℕ} (T : ℕ)
    {xs : List (Fin n)} (h : xs ∈ finiteSuccessorWords n (T+1)) :
    xs ≠ [] := by
  intro he
  subst xs
  simp [finiteSuccessorWords] at h

private theorem successorWordWins_initialGoal {n : ℕ}
    (target : RationalHittingTarget n) (T : ℕ) (y : Fin n)
    (hy : y ∈ target.goal)
    {xs : List (Fin n)} (hx : xs ∈ finiteSuccessorWords n (T+1)) :
    successorWordWins target y xs = true := by
  cases xs with
  | nil => exact (finiteSuccessorWords_succ_nonempty T hx rfl).elim
  | cons z zs => simp [successorWordWins, hy]

private theorem successorWordWins_initialForbidden {n : ℕ}
    (target : RationalHittingTarget n) (T : ℕ) (y : Fin n)
    (hy : y ∉ target.goal) (hd : y ∈ target.forbidden)
    {xs : List (Fin n)} (hx : xs ∈ finiteSuccessorWords n (T+1)) :
    successorWordWins target y xs = false := by
  cases xs with
  | nil => exact (finiteSuccessorWords_succ_nonempty T hx rfl).elim
  | cons z zs => simp [successorWordWins, hy, hd]

/-- Independent full-path enumeration satisfies the same recursion as the
backwards solver; the proof does not assume or unfold rationalHittingValue. -/
theorem rationalForwardEnumeration_succ {n : ℕ} (K : RationalMarkovMatrix n)
    (target : RationalHittingTarget n) (T : ℕ) (y : Fin n) :
    rationalForwardEnumeration K target (T+1) y =
      if y ∈ target.goal then 1
      else if y ∈ target.forbidden then 0
      else ∑ z : Fin n, K.entry y z *
        rationalForwardEnumeration K target T z := by
  by_cases hg : y ∈ target.goal
  · rw [if_pos hg]
    have hmass := successorWordMass_total K (T+1) y
    have h :
        rationalForwardEnumeration K target (T+1) y =
          ((finiteSuccessorWords n (T+1)).map (successorWordMass K y)).sum := by
      unfold rationalForwardEnumeration
      congr 1
      apply List.map_congr_left
      intro xs hx
      simp [successorWordWins_initialGoal target T y hg hx]
    exact h.trans hmass
  · rw [if_neg hg]
    by_cases hd : y ∈ target.forbidden
    · rw [if_pos hd]
      unfold rationalForwardEnumeration
      have h :
          ((finiteSuccessorWords n (T+1)).map
            (fun xs => successorWordMass K y xs *
              (if successorWordWins target y xs then (1 : ℚ) else 0))).sum =
              ((finiteSuccessorWords n (T+1)).map (fun _ => (0 : ℚ))).sum := by
        congr 1
        apply List.map_congr_left
        intro xs hx
        simp [successorWordWins_initialForbidden target T y hg hd hx]
      rw [h]
      simp
    · rw [if_neg hd]
      unfold rationalForwardEnumeration
      simp only [finiteSuccessorWords, sum_map_flatMap]
      rw [sum_map_finRange]
      apply Finset.sum_congr rfl
      intro z hz
      simp only [List.map_map]
      have hfactor : ∀ xs : List (Fin n),
          successorWordMass K y (z :: xs) *
            (if successorWordWins target y (z :: xs) then (1 : ℚ) else 0) =
          K.entry y z * (successorWordMass K z xs *
            (if successorWordWins target z xs then (1 : ℚ) else 0)) := by
        intro xs
        simp [successorWordMass, successorWordWins, hg, hd, mul_assoc]
      simp only [Function.comp_def, hfactor, List.sum_map_mul_left]

/-- Independent weighted enumeration and the backward recurrence agree
for every certified rational matrix, starting state and finite horizon. -/
theorem rationalForwardEnumeration_eq_recursion {n : ℕ}
    (K : RationalMarkovMatrix n) (target : RationalHittingTarget n) :
    ∀ (T : ℕ) (y : Fin n),
      rationalForwardEnumeration K target T y =
        rationalHittingValue K target T y := by
  intro T
  induction T with
  | zero =>
      intro y
      simp [rationalForwardEnumeration, finiteSuccessorWords,
        successorWordMass, successorWordWins, rationalHittingValue]
  | succ T ih =>
      intro y
      rw [rationalForwardEnumeration_succ, rationalHittingValue_succ]
      split_ifs
      · rfl
      · rfl
      · simp_rw [ih]

end ReverseSolver
end PermanssonResearch
