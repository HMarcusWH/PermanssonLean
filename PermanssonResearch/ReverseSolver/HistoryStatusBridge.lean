import PermanssonResearch.ReverseSolver.HistoryContinuation
import PermanssonResearch.ReverseSolver.CanonicalWordEvent
import Mathlib.Tactic

/-!
# D1-D1: terminal-history status matches the ORIGINAL first-hit event

Winning must mean the goal was reached before the first forbidden visit.
A later goal cannot undo a previously recorded loss; a later forbidden
visit cannot undo an earlier win. This is pure path-event semantics and
does not pretend the transition kernel physically absorbs terminal states.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependent

/-- The three-state historical status recursion agrees with D0's independently
proved successor-word first-hit Boolean, for every word and initial state. -/
theorem foldl_status_won_iff_successorWordWins {n : ℕ}
    (target : RationalHittingTarget n) :
    ∀ (xs : List (Fin n)) (y : Fin n),
      (xs.foldl (advanceStatus target) (initialStatus target y) = .won) ↔
        successorWordWins target y xs = true := by
  intro xs
  induction xs with
  | nil =>
      intro y
      by_cases hg : y ∈ target.goal
      · simp [initialStatus, advanceStatus, successorWordWins, hg]
      · by_cases hf : y ∈ target.forbidden
        · simp [initialStatus, advanceStatus, successorWordWins, hg, hf]
        · simp [initialStatus, advanceStatus, successorWordWins, hg, hf]
  | cons z zs ih =>
      intro y
      by_cases hg : y ∈ target.goal
      · simp [initialStatus, advanceStatus, successorWordWins, hg,
          foldl_status_won]
      · by_cases hf : y ∈ target.forbidden
        · simp [initialStatus, advanceStatus, successorWordWins, hg, hf,
            foldl_status_lost]
        · have hnext : advanceStatus target (initialStatus target y) z =
              initialStatus target z := by
            simp [initialStatus, advanceStatus, hg, hf]
          simpa [List.foldl_cons, hnext, successorWordWins, hg, hf] using ih z

/-- COMPLETE measured-prefix win classification: the historical status
matches the original D0 measurable goal-before-forbidden event. -/
theorem foldl_status_won_iff_successPrefixEvent {n : ℕ}
    (target : RationalHittingTarget n) (t : ℕ)
    (w : (i : Finset.Iic t) → Fin n) :
    ((List.ofFn (stepsFromHistory t w)).foldl (advanceStatus target)
        (initialStatus target
          (w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩)) = .won) ↔
      w ∈ successPrefixEvent (rationalTargetAsFrozen target) t := by
  let x := w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩
  let steps := stepsFromHistory t w
  have hevent := canonicalSuccess_iff_wordWins target t x steps
  have hhistory : historyFromSteps t x steps = w :=
    historyFromSteps_stepsFromHistory t x w rfl
  rw [hhistory] at hevent
  exact (foldl_status_won_iff_successorWordWins target (List.ofFn steps) x).trans
    hevent.symm

end HistoryDependent
end ReverseSolver
end PermanssonResearch
