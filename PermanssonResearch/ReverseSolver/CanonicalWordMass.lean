import PermanssonResearch.ReverseSolver.CanonicalWordEvent
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# D0-C: original rational successor-word weights equal chronological products

Uses the *existing* D0-B successorWordMass recursion and the *existing*
rational matrix entry function; no substitute evaluator or numerical
approximation is introduced.
-/

namespace PermanssonResearch
namespace ReverseSolver

private theorem historyFromSteps_shift {n : ℕ}
    (T : ℕ) (y : Fin n) (v : Fin (T+1) → Fin n)
    (i : Fin (T+1)) :
    historyFromSteps (T+1) y v
      ⟨i.val+1, Finset.mem_Iic.mpr (Nat.succ_le_of_lt i.isLt)⟩ =
    historyFromSteps T (v 0) (Fin.tail v)
      ⟨i.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩ := by
  change Fin.cons y v (Fin.succ i) =
    Fin.cons (v 0) (Fin.tail v) i
  rw [Fin.cons_succ, Fin.cons_self_tail]

/-- Factor the chronological rational weight at its *first* transition.
The tail then has the actual first successor as its new starting point. -/
theorem rationalHistoryWeight_head {n : ℕ}
    (M : RationalMarkovMatrix n) (T : ℕ)
    (y : Fin n) (v : Fin (T+1) → Fin n) :
    rationalHistoryWeight M (T+1) (historyFromSteps (T+1) y v) =
      M.entry y (v 0) *
        rationalHistoryWeight M T
          (historyFromSteps T (v 0) (Fin.tail v)) := by
  classical
  unfold rationalHistoryWeight
  rw [Fin.prod_univ_succ]
  congr 1
  · simp [historyFromSteps, historyTimeEquiv, Fin.cons_zero, Fin.cons_succ]
  · apply Finset.prod_congr rfl
    intro i _
    have h1 := historyFromSteps_shift T y v (Fin.castSucc i)
    have h2 := historyFromSteps_shift T y v (Fin.succ i)
    simpa [Fin.val_castSucc, Fin.val_succ] using
      congrArg₂ M.entry h1 h2

/-- The exact D0-B word-mass recursion agrees with the rational product
along its canonical fixed-initial-state history for every finite horizon. -/
theorem successorWordMass_ofFn_eq_rationalHistoryWeight {n : ℕ}
    (M : RationalMarkovMatrix n) :
    ∀ (T : ℕ) (y : Fin n) (v : Fin T → Fin n),
      successorWordMass M y (List.ofFn v) =
        rationalHistoryWeight M T (historyFromSteps T y v) := by
  intro T
  induction T with
  | zero =>
      intro y v
      simp [rationalHistoryWeight, successorWordMass, List.ofFn_zero]
  | succ T ih =>
      intro y v
      rw [List.ofFn_succ]
      change M.entry y (v 0) *
          successorWordMass M (v 0) (List.ofFn (Fin.tail v)) =
        rationalHistoryWeight M (T+1) (historyFromSteps (T+1) y v)
      rw [rationalHistoryWeight_head]
      rw [ih (v 0) (Fin.tail v)]

end ReverseSolver
end PermanssonResearch
