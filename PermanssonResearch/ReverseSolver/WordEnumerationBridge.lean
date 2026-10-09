import PermanssonResearch.ReverseSolver.RationalHistoryProduct
import PermanssonResearch.ReverseSolver.FiniteEvaluation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# D0-C: finite-word enumeration equals a sum over successor vectors

The existing D0-B forward evaluator enumerates all successor words.
This lemma identifies the exact enumeration (including multiplicity) with
functions on Fin T, which are the successors in the canonical history.
-/

namespace PermanssonResearch
namespace ReverseSolver

private theorem sum_map_flatMap_word {α β : Type*}
    (xs : List α) (f : α → List β) (g : β → ℚ) :
    ((xs.flatMap f).map g).sum =
      (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

private theorem sum_map_finRange_word (n : ℕ) (g : Fin n → ℚ) :
    ((List.finRange n).map g).sum = ∑ z : Fin n, g z := by
  rw [← List.sum_toFinset g (List.nodup_finRange n)]
  simp

/-- The complete list of length-T successor words integrates any rational
test function exactly as the finite sum over all Fin T state vectors. -/
theorem finiteSuccessorWords_sum_eq_vectorSum (n : ℕ) :
    ∀ (T : ℕ) (f : List (Fin n) → ℚ),
      ((finiteSuccessorWords n T).map f).sum =
        ∑ v : Fin T → Fin n, f (List.ofFn v) := by
  intro T
  induction T with
  | zero =>
      intro f
      classical
      simp [finiteSuccessorWords, List.ofFn_zero]
  | succ T ih =>
      intro f
      classical
      calc
        ((finiteSuccessorWords n (T+1)).map f).sum =
          ((List.finRange n).map (fun z =>
            ((finiteSuccessorWords n T).map
              (fun xs => f (z :: xs))).sum)).sum := by
                simp [finiteSuccessorWords, sum_map_flatMap_word,
                  List.map_map, Function.comp_def]
        _ = ∑ z : Fin n, ∑ v : Fin T → Fin n,
              f (z :: List.ofFn v) := by
                rw [sum_map_finRange_word]
                congr 1
                funext z
                exact ih (fun xs => f (z :: xs))
        _ = ∑ p : Fin n × (Fin T → Fin n),
              f (p.1 :: List.ofFn p.2) := by
                rw [Fintype.sum_prod_type]
        _ = ∑ v : Fin (T+1) → Fin n, f (List.ofFn v) := by
                symm
                apply Fintype.sum_equiv
                  (Fin.consEquiv (fun _ : Fin (T+1) => Fin n))
                intro v
                simp [Fin.consEquiv, List.ofFn_succ]

end ReverseSolver
end PermanssonResearch
