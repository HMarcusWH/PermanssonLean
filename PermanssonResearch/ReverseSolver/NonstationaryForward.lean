import PermanssonResearch.ReverseSolver.NonstationaryHitting
import PermanssonResearch.ReverseSolver.CanonicalWordMass
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# D1-C1: independent first-successor exact rational forward evaluation

The forward witness enumerates all length-T successor lists, using the
currently remaining horizon for each transition and the original
goal-before-forbidden word predicate. The forward rational recursion
is proved equal to D1-B's policyValue without assuming any measure
correspondence. Separately, the path-product relation identifies these
independent forward weights with the true nonstationary trajectory atoms.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace Nonstationary

open Bellman
open ControlledKernel

universe uC

/-- The genuine forward word weight with the correct countdown.
The nominal remaining argument is decremented only after each transition. -/
def remainingWordMass {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (remaining : ℕ) (y : Fin n) : List (Fin n) → ℚ
  | [] => 1
  | z :: zs =>
      (feedbackMatrix sys (π remaining)).entry y z *
        remainingWordMass sys π (remaining-1) z zs

/-- Exhaustive rational forward sum, independently of the Bellman evaluator. -/
def forwardEnumeration {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (target : RationalHittingTarget n) (T : ℕ) (y : Fin n) : ℚ :=
  ((finiteSuccessorWords n T).map fun xs =>
    remainingWordMass sys π T y xs *
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

/-- For every permitted remaining-horizon Markov schedule, all complete
successor words at any horizon have total mass exactly one. -/
theorem remainingWordMass_total {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys) :
    ∀ (T : ℕ) (y : Fin n),
      ((finiteSuccessorWords n T).map
        (remainingWordMass sys π T y)).sum = 1 := by
  intro T
  induction T with
  | zero =>
      intro y
      simp [finiteSuccessorWords, remainingWordMass]
  | succ T ih =>
      intro y
      calc
        ((finiteSuccessorWords n (T+1)).map
            (remainingWordMass sys π (T+1) y)).sum =
          ((List.finRange n).map (fun z =>
            ((finiteSuccessorWords n T).map
              (fun xs => (feedbackMatrix sys (π (T+1))).entry y z *
                remainingWordMass sys π T z xs)).sum)).sum := by
              simp [finiteSuccessorWords, sum_map_flatMap, List.map_map,
                Function.comp_def, remainingWordMass]
        _ = ((List.finRange n).map
            (fun z => (feedbackMatrix sys (π (T+1))).entry y z)).sum := by
              simp [List.sum_map_mul_left, ih]
        _ = 1 := by
              rw [sum_map_finRange, (feedbackMatrix sys (π (T+1))).row_sum_one]

/-- Exact rational first-step recursion for the independent exhaustive
word enumeration, including goal/forbidden time-zero boundaries. -/
theorem forwardEnumeration_succ {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (target : RationalHittingTarget n) (T : ℕ) (y : Fin n) :
    forwardEnumeration sys π target (T+1) y =
      if y ∈ target.goal then 1
      else if y ∈ target.forbidden then 0
      else ∑ z : Fin n,
          (feedbackMatrix sys (π (T+1))).entry y z *
            forwardEnumeration sys π target T z := by
  by_cases hg : y ∈ target.goal
  · rw [if_pos hg]
    have hmass := remainingWordMass_total sys π (T+1) y
    have h : forwardEnumeration sys π target (T+1) y =
        ((finiteSuccessorWords n (T+1)).map
          (remainingWordMass sys π (T+1) y)).sum := by
      unfold forwardEnumeration
      congr 1
      apply List.map_congr_left
      intro xs hx
      have hnonempty : xs ≠ [] := by
        intro he
        subst xs
        simp [finiteSuccessorWords] at hx
      cases xs with
      | nil => exact (hnonempty rfl).elim
      | cons z zs => simp [successorWordWins, hg]
    exact h.trans hmass
  · rw [if_neg hg]
    by_cases hd : y ∈ target.forbidden
    · rw [if_pos hd]
      unfold forwardEnumeration
      have h : ((finiteSuccessorWords n (T+1)).map
          (fun xs => remainingWordMass sys π (T+1) y xs *
            (if successorWordWins target y xs then (1 : ℚ) else 0))).sum =
          ((finiteSuccessorWords n (T+1)).map (fun _ => (0 : ℚ))).sum := by
        congr 1
        apply List.map_congr_left
        intro xs hx
        have hnonempty : xs ≠ [] := by
          intro he
          subst xs
          simp [finiteSuccessorWords] at hx
        cases xs with
        | nil => exact (hnonempty rfl).elim
        | cons z zs => simp [successorWordWins, hg, hd]
      rw [h]
      simp
    · rw [if_neg hd]
      unfold forwardEnumeration
      simp only [finiteSuccessorWords, sum_map_flatMap]
      rw [sum_map_finRange]
      apply Finset.sum_congr rfl
      intro z hz
      simp only [List.map_map]
      have hfactor : ∀ xs : List (Fin n),
          remainingWordMass sys π (T+1) y (z :: xs) *
            (if successorWordWins target y (z :: xs) then (1 : ℚ) else 0) =
          (feedbackMatrix sys (π (T+1))).entry y z *
            (remainingWordMass sys π T z xs *
              (if successorWordWins target z xs then (1 : ℚ) else 0)) := by
        intro xs
        simp [remainingWordMass, successorWordWins, hg, hd, mul_assoc]
      simp only [Function.comp_def, hfactor, List.sum_map_mul_left]

/-- Exact forward enumeration equals D1-B's original recursive policyValue
at EVERY horizon and initial state. -/
theorem forwardEnumeration_eq_policyValue {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (target : RationalHittingTarget n) :
    ∀ (T : ℕ) (y : Fin n),
      forwardEnumeration sys π target T y =
        policyValue sys target π T y := by
  intro T
  induction T with
  | zero =>
      intro y
      simp [forwardEnumeration, finiteSuccessorWords,
        remainingWordMass, successorWordWins, policyValue]
  | succ T ih =>
      intro y
      rw [forwardEnumeration_succ, policyValue_succ]
      split_ifs
      · rfl
      · rfl
      · simp_rw [ih]
        rfl

/-- Shift one coordinate from the current first-step path to its tail. -/
private theorem historyFromSteps_shift {n : ℕ}
    (T : ℕ) (y : Fin n) (v : Fin (T+1) → Fin n)
    (i : Fin (T+1)) :
    historyFromSteps (T+1) y v
      ⟨i.val+1, Finset.mem_Iic.mpr
        (Nat.succ_le_of_lt i.isLt)⟩ =
    historyFromSteps T (v 0) (Fin.tail v)
      ⟨i.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩ := by
  change (Fin.cons y v : Fin (T+2) → Fin n) (Fin.succ i) =
    (Fin.cons (v 0) (Fin.tail v) : Fin (T+1) → Fin n) i
  rw [Fin.cons_succ, Fin.cons_self_tail]

/-- The complete path-product weight factors at the FIRST control step,
with the remaining original horizon decreasing by one. -/
theorem rationalPathWeight_head {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T : ℕ) (y : Fin n) (v : Fin (T+1) → Fin n) :
    rationalPathWeight sys π (T+1) (T+1)
      (historyFromSteps (T+1) y v) =
    (feedbackMatrix sys (π (T+1))).entry y (v 0) *
      rationalPathWeight sys π T T
        (historyFromSteps T (v 0) (Fin.tail v)) := by
  classical
  unfold rationalPathWeight
  rw [Fin.prod_univ_succ]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have h1 := historyFromSteps_shift T y v (Fin.castSucc i)
  have h2 := historyFromSteps_shift T y v (Fin.succ i)
  have hindex : (T+1) - ((i : Fin T).val+1) = T - i.val := by
    omega
  simpa [selectedMatrix, hindex, Fin.val_castSucc, Fin.val_succ] using
    congrArg₂ (fun a b => (feedbackMatrix sys (π (T-i.val))).entry a b)
      h1 h2

/-- The genuinely chronological rational product equals the independent
remaining-horizon forward word mass, at every length and initial state. -/
theorem remainingWordMass_ofFn_eq_pathWeight
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys) :
    ∀ (T : ℕ) (y : Fin n) (v : Fin T → Fin n),
      remainingWordMass sys π T y (List.ofFn v) =
        rationalPathWeight sys π T T (historyFromSteps T y v) := by
  intro T
  induction T with
  | zero =>
      intro y v
      simp [remainingWordMass, rationalPathWeight, List.ofFn_zero]
  | succ T ih =>
      intro y v
      rw [List.ofFn_succ]
      change (feedbackMatrix sys (π (T+1))).entry y (v 0) *
          remainingWordMass sys π T (v 0) (List.ofFn (Fin.tail v)) =
        rationalPathWeight sys π (T+1) (T+1)
          (historyFromSteps (T+1) y v)
      rw [rationalPathWeight_head]
      rw [ih (v 0) (Fin.tail v)]

end Nonstationary
end ReverseSolver
end PermanssonResearch
