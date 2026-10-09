import PermanssonResearch.ReverseSolver.WordEnumerationBridge
import Mathlib.Tactic

/-!
# D0-C: first-goal-before-forbidden on finite successor vectors

The event is expressed as an existential witness at a concrete time index
with the forbidden condition at every strictly earlier index. Its recursion
preserves time zero, strict precedence and nonabsorbing transitions.
-/

namespace PermanssonResearch
namespace ReverseSolver

/-- Chronological goal-before-forbidden predicate for a complete Fin(T+1)
history, independent of any stochastic measure. -/
def finiteVectorSuccess {n : ℕ}
    (target : RationalHittingTarget n) (T : ℕ)
    (v : Fin (T+1) → Fin n) : Prop :=
  ∃ t : Fin (T+1), v t ∈ target.goal ∧
    ∀ u : Fin (T+1), u < t → v u ∉ target.forbidden

/-- The initial state is checked before any transition; otherwise the
event is exactly the same event for the successor vector. -/
theorem finiteVectorSuccess_cons {n : ℕ}
    (target : RationalHittingTarget n) (T : ℕ)
    (y : Fin n) (v : Fin (T+1) → Fin n) :
    finiteVectorSuccess target (T+1) (Fin.cons y v) ↔
      y ∈ target.goal ∨
        (y ∉ target.forbidden ∧ finiteVectorSuccess target T v) := by
  classical
  constructor
  · rintro ⟨t, ht, hbefore⟩
    cases t using Fin.cases with
    | zero =>
        exact Or.inl (by simpa only [Fin.cons_zero] using ht)
    | succ t =>
        right
        refine ⟨?_, ⟨t, by simpa only [Fin.cons_succ] using ht, ?_⟩⟩
        · have h := hbefore 0 (by simp)
          simpa only [Fin.cons_zero] using h
        · intro u hu
          have h := hbefore (Fin.succ u) (by simpa using hu)
          simpa only [Fin.cons_succ] using h
  · rintro (hy | ⟨hnot, ⟨t, ht, hbefore⟩⟩)
    · refine ⟨0, by simpa only [Fin.cons_zero] using hy, ?_⟩
      intro u hu
      exact (not_lt_zero' hu).elim
    · refine ⟨Fin.succ t, by simpa only [Fin.cons_succ] using ht, ?_⟩
      intro u hu
      cases u using Fin.cases with
      | zero =>
          simpa only [Fin.cons_zero] using hnot
      | succ u =>
          have hlt : u < t := by simpa using hu
          simpa only [Fin.cons_succ] using hbefore u hlt

end ReverseSolver
end PermanssonResearch
