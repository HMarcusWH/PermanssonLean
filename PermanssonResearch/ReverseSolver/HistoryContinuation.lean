import PermanssonResearch.ReverseSolver.HistoryEventValue
import PermanssonResearch.ReverseSolver.NonstationaryForward
import Mathlib.Tactic

/-!
# D1-D1: exact rational continuations over complete observed histories

This evaluator enumerates ALL successor words. It carries an explicit
first-hit status to distinguish success-before-danger, danger-before-success,
and unresolved histories, including after physical paths leave terminal
regions. It never conditions on a possibly zero-mass observed prefix.

A separate all-path bridge must show equality of this forward calculation
with the original D0 event under the genuine partialTraj measure.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependent

open ControlledKernel
open Bellman

universe uC

/-- Finite-horizon first-hit evaluation remembers the first terminal event.
A terminal classification does not physically modify a transition row. -/
inductive HitStatus where
  | unresolved
  | won
  | lost
  deriving DecidableEq, Repr

/-- Consume a newly observed state, preserving previous terminal outcomes. -/
def advanceStatus {n : ℕ} (target : RationalHittingTarget n) :
    HitStatus → Fin n → HitStatus
  | .won, _ => .won
  | .lost, _ => .lost
  | .unresolved, z =>
      if z ∈ target.goal then .won
      else if z ∈ target.forbidden then .lost
      else .unresolved

/-- The initial observation counts towards the first-hit event. -/
def initialStatus {n : ℕ} (target : RationalHittingTarget n)
    (x : Fin n) : HitStatus :=
  advanceStatus target .unresolved x

/-- Append one newly observed state, with no access to any future state. -/
def appendHistory {n i : ℕ} (h : History n i) (z : Fin n) :
    History n (i+1) :=
  fun j =>
    if hj : (j : ℕ) ≤ i then
      h ⟨j.val, Finset.mem_Iic.mpr hj⟩
    else z

@[simp] theorem appendHistory_last {n i : ℕ}
    (h : History n i) (z : Fin n) :
    last (appendHistory h z) = z := by
  simp [last, appendHistory]

@[simp] theorem appendHistory_old {n i : ℕ}
    (h : History n i) (z : Fin n) (j : Finset.Iic i) :
    appendHistory h z
      ⟨j.val, Finset.mem_Iic.mpr
        (Nat.le_trans (Finset.mem_Iic.mp j.property) (Nat.le_succ i))⟩ = h j := by
  simp [appendHistory, Finset.mem_Iic.mp j.property]

/-- Exact rational probability of a future successor list, using complete
history to select every transition row at the actual chronological step. -/
def completionMass {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (h : History n i) : List (Fin n) → ℚ
  | [] => 1
  | z :: zs =>
      selectedEntry sys σ D i h z *
      completionMass sys σ D (i+1) (appendHistory h z) zs

/-- Independent rational forward evaluation. The probability of success is
computed from complete successor words with first-hit status memory. -/
def forwardValue {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (target : RationalHittingTarget n) (D i : ℕ)
    (h : History n i) (status : HitStatus) (r : ℕ) : ℚ :=
  ((finiteSuccessorWords n r).map fun xs =>
    completionMass sys σ D i h xs *
      (if xs.foldl (advanceStatus target) status = .won then
        (1 : ℚ) else 0)).sum

private theorem sum_map_flatMap {α β : Type*}
    (xs : List α) (f : α → List β) (g : β → ℚ) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

private theorem sum_map_finRange (n : ℕ) (g : Fin n → ℚ) :
    ((List.finRange n).map g).sum = ∑ z : Fin n, g z := by
  rw [← List.sum_toFinset g (List.nodup_finRange n)]
  simp

/-- All length-r successor words carry unit total rational mass from EVERY
supplied prefix, including prefixes with zero probability in the actual run. -/
theorem completionMass_total {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys) (D : ℕ) :
    ∀ (r i : ℕ) (h : History n i),
      ((finiteSuccessorWords n r).map (completionMass sys σ D i h)).sum = 1 := by
  intro r
  induction r with
  | zero =>
      intro i h
      simp [finiteSuccessorWords, completionMass]
  | succ r ih =>
      intro i h
      calc
        ((finiteSuccessorWords n (r+1)).map
            (completionMass sys σ D i h)).sum =
          ((List.finRange n).map (fun z =>
            ((finiteSuccessorWords n r).map
              (fun xs => selectedEntry sys σ D i h z *
                completionMass sys σ D (i+1) (appendHistory h z) xs)).sum)).sum := by
            simp [finiteSuccessorWords, sum_map_flatMap, List.map_map,
              completionMass, Function.comp_def]
        _ = ((List.finRange n).map
              (fun z => selectedEntry sys σ D i h z)).sum := by
            simp [List.sum_map_mul_left, ih]
        _ = 1 := by
            rw [sum_map_finRange, selectedEntry_row_sum_one]

/-- Forward history evaluation satisfies its exact chronological
first-successor recursion, with no claim about a stationary path law. -/
theorem forwardValue_succ {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (target : RationalHittingTarget n) (D i r : ℕ)
    (h : History n i) (s : HitStatus) :
    forwardValue sys σ target D i h s (r+1) =
      ∑ z : Fin n, selectedEntry sys σ D i h z *
        forwardValue sys σ target D (i+1)
          (appendHistory h z) (advanceStatus target s z) r := by
  unfold forwardValue
  simp only [finiteSuccessorWords, sum_map_flatMap]
  rw [sum_map_finRange]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [List.map_map]
  have hfactor : ∀ xs : List (Fin n),
      completionMass sys σ D i h (z :: xs) *
        (if (z :: xs).foldl (advanceStatus target) s = .won then
          (1 : ℚ) else 0) =
      selectedEntry sys σ D i h z *
        (completionMass sys σ D (i+1) (appendHistory h z) xs *
          (if xs.foldl (advanceStatus target) (advanceStatus target s z) = .won
            then (1 : ℚ) else 0)) := by
    intro xs
    by_cases hw : xs.foldl (advanceStatus target) (advanceStatus target s z) = .won
    · simp [completionMass, List.foldl_cons, hw, mul_assoc]
    · simp [completionMass, List.foldl_cons, hw]
  simp only [Function.comp_def, hfactor, List.sum_map_mul_left]

theorem foldl_status_won {n : ℕ} (target : RationalHittingTarget n) :
    ∀ xs : List (Fin n),
      xs.foldl (advanceStatus target) .won = .won := by
  intro xs
  induction xs with
  | nil => rfl
  | cons z zs ih =>
      simpa [List.foldl_cons, advanceStatus] using ih

theorem foldl_status_lost {n : ℕ} (target : RationalHittingTarget n) :
    ∀ xs : List (Fin n),
      xs.foldl (advanceStatus target) .lost = .lost := by
  intro xs
  induction xs with
  | nil => rfl
  | cons z zs ih =>
      simpa [List.foldl_cons, advanceStatus] using ih

/-- Once won, success value stays one even after later forbidden visits. -/
theorem forwardValue_won {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (target : RationalHittingTarget n) (D i r : ℕ)
    (h : History n i) :
    forwardValue sys σ target D i h .won r = 1 := by
  unfold forwardValue
  simpa [foldl_status_won] using completionMass_total sys σ D r i h

/-- Once lost, no later goal entry can revive a failed first-hit event. -/
theorem forwardValue_lost {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (target : RationalHittingTarget n) (D i r : ℕ)
    (h : History n i) :
    forwardValue sys σ target D i h .lost r = 0 := by
  simp [forwardValue, foldl_status_lost]

/-- A full observed history can never improve the exact Bellman value when
the first-hit objective is still unresolved. This compares the independent
rational continuation enumerator; law/event correspondence comes next. -/
theorem forwardValue_unresolved_le_bellman
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (target : RationalHittingTarget n) (D : ℕ) :
    ∀ (r i : ℕ) (h : History n i),
      last h ∉ target.goal → last h ∉ target.forbidden →
      forwardValue sys σ target D i h .unresolved r ≤
        bellmanValue sys target r (last h) := by
  intro r
  induction r with
  | zero =>
      intro i h hg hf
      have hb := (bellmanValue_bounds sys target 0 (last h)).1
      simpa [forwardValue, finiteSuccessorWords, completionMass] using hb
  | succ r ih =>
      intro i h hg hf
      rw [forwardValue_succ, bellmanValue_succ]
      simp only [if_neg hg, if_neg hf]
      calc
        (∑ z : Fin n, selectedEntry sys σ D i h z *
          forwardValue sys σ target D (i+1)
            (appendHistory h z) (advanceStatus target .unresolved z) r) ≤
          ∑ z : Fin n, selectedEntry sys σ D i h z *
            bellmanValue sys target r z := by
              apply Finset.sum_le_sum
              intro z _
              apply mul_le_mul_of_nonneg_left ?_ (selectedEntry_nonneg sys σ D i h z)
              by_cases hgoal : z ∈ target.goal
              · rw [show advanceStatus target .unresolved z = .won by
                    simp [advanceStatus, hgoal]]
                rw [forwardValue_won, bellmanValue_goal sys target r z hgoal]
              · by_cases hbad : z ∈ target.forbidden
                · rw [show advanceStatus target .unresolved z = .lost by
                      simp [advanceStatus, hgoal, hbad]]
                  rw [forwardValue_lost, bellmanValue_forbidden sys target r z hbad]
                · rw [show advanceStatus target .unresolved z = .unresolved by
                      simp [advanceStatus, hgoal, hbad]]
                  simpa only [appendHistory_last] using
                    (ih (i+1) (appendHistory h z) (by simpa using hgoal)
                      (by simpa using hbad))
        _ ≤ actionScore sys (bellmanValue sys target r) (last h)
            (bestControl sys (bellmanValue sys target r) (last h)) := by
              simpa [selectedEntry, actionScore] using
                (bestControl_dominates sys (bellmanValue sys target r)
                  (last h) (σ.choose D i h) (σ.permitted D i h))

/-- Every history-dependent policy's INDEPENDENT exact rational forward
evaluation from the original initial state is Bellman-bounded. This is not
yet the statement about the genuine trajectory event measure; connecting
the forward evaluator to that measure is the remaining D1-D1 bridge. -/
theorem forwardValue_initial_le_bellman
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    forwardValue sys σ target D 0 (singletonPrefix x)
      (initialStatus target x) D ≤ bellmanValue sys target D x := by
  by_cases hg : x ∈ target.goal
  · have hs : initialStatus target x = .won := by
      simp [initialStatus, advanceStatus, hg]
    rw [hs, forwardValue_won, bellmanValue_goal sys target D x hg]
  · by_cases hf : x ∈ target.forbidden
    · have hs : initialStatus target x = .lost := by
        simp [initialStatus, advanceStatus, hg, hf]
      rw [hs, forwardValue_lost, bellmanValue_forbidden sys target D x hf]
    · have hs : initialStatus target x = .unresolved := by
        simp [initialStatus, advanceStatus, hg, hf]
      rw [hs]
      simpa [last, singletonPrefix] using
        (forwardValue_unresolved_le_bellman sys σ target D D 0
          (singletonPrefix x) (by simpa [last, singletonPrefix] using hg)
          (by simpa [last, singletonPrefix] using hf))

end HistoryDependent
end ReverseSolver
end PermanssonResearch
