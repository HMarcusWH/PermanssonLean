import PermanssonResearch.ReverseSolver.CanonicalEventVectorEquiv
import Mathlib.Tactic

/-!
# D0-C: exact equivalence of successor-word win Boolean and canonical event

The original D0-B `successorWordWins` recursion is shown equivalent to the
goal-before-forbidden vector predicate, without replacing either definition.
-/

namespace PermanssonResearch
namespace ReverseSolver

/-- For any horizon, the original word-event evaluator and the independent
finite-vector first-hitting predicate agree exactly. -/
theorem finiteVectorSuccess_iff_successorWordWins {n : ℕ}
    (target : RationalHittingTarget n) :
    ∀ (T : ℕ) (y : Fin n) (steps : Fin T → Fin n),
      finiteVectorSuccess target T (Fin.cons y steps) ↔
        successorWordWins target y (List.ofFn steps) = true := by
  intro T
  induction T with
  | zero =>
      intro y steps
      have he :
          finiteVectorSuccess target 0 (Fin.cons y steps) ↔
            y ∈ target.goal := by
        unfold finiteVectorSuccess
        constructor
        · rintro ⟨t, ht, _⟩
          have hzero : t = 0 := Fin.fin_one_eq_zero t
          subst t
          simpa only [Fin.cons_zero] using ht
        · intro hy
          refine ⟨0, by simpa only [Fin.cons_zero] using hy, ?_⟩
          intro u hu
          exact (not_lt_zero' u hu).elim
      simpa [List.ofFn_zero, successorWordWins] using he
  | succ T ih =>
      intro y steps
      have ht : Fin.cons (steps 0) (Fin.tail steps) = steps :=
        Fin.cons_self_tail steps
      have hs := ih (steps 0) (Fin.tail steps)
      rw [ht] at hs
      rw [finiteVectorSuccess_cons]
      rw [List.ofFn_succ]
      change
        (y ∈ target.goal ∨
          (y ∉ target.forbidden ∧ finiteVectorSuccess target T steps)) ↔
        successorWordWins target y
          (steps 0 :: List.ofFn (Fin.tail steps)) = true
      by_cases hg : y ∈ target.goal
      · simp [successorWordWins, hg]
      · by_cases hd : y ∈ target.forbidden
        · simp [successorWordWins, hg, hd]
        · simpa [successorWordWins, hg, hd] using hs

/-- The original D0-B Boolean and the literal canonical path event agree,
for every finite list represented by its successor vector. -/
theorem canonicalSuccess_iff_wordWins {n : ℕ}
    (target : RationalHittingTarget n) (T : ℕ)
    (y : Fin n) (steps : Fin T → Fin n) :
    historyFromSteps T y steps ∈
        successPrefixEvent (rationalTargetAsFrozen target) T ↔
      successorWordWins target y (List.ofFn steps) = true := by
  exact (successPrefixEvent_historyFromSteps_iff target T y steps).trans
    (finiteVectorSuccess_iff_successorWordWins target T y steps)

end ReverseSolver
end PermanssonResearch
