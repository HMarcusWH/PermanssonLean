import PermanssonResearch.ReverseSolver.CanonicalHistoryAtoms
import Mathlib.Tactic

/-!
# D0-C: indexing the canonical history by its T successor states

The endpoint-inclusive history index `Finset.Iic T` has exactly T+1
coordinates. Its initial coordinate is y; the other T form the complete
successor word. All transformations below are pure finite bijections.
-/

namespace PermanssonResearch
namespace ReverseSolver

/-- An endpoint-inclusive natural history index is a Fin(T+1) index. -/
def historyTimeEquiv (T : ℕ) : Finset.Iic T ≃ Fin (T+1) where
  toFun i := ⟨i.val, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.property)⟩
  invFun j := ⟨j.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ j.isLt)⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv j := by apply Fin.ext; rfl

/-- History with the frozen initial state and the given T successors. -/
def historyFromSteps {n : ℕ} (T : ℕ) (y : Fin n)
    (steps : Fin T → Fin n) : (i : Finset.Iic T) → Fin n :=
  fun i => (Fin.cons y steps : Fin (T+1) → Fin n) (historyTimeEquiv T i)

/-- Extract the T successors at times 1 through T. -/
def stepsFromHistory {n : ℕ} (T : ℕ)
    (w : (i : Finset.Iic T) → Fin n) : Fin T → Fin n :=
  fun j => w ((historyTimeEquiv T).symm (Fin.succ j))

@[simp] theorem historyFromSteps_initial {n : ℕ} (T : ℕ)
    (y : Fin n) (steps : Fin T → Fin n) :
    historyFromSteps T y steps
      ⟨0, Finset.mem_Iic.mpr (Nat.zero_le T)⟩ = y := by
  simp [historyFromSteps, historyTimeEquiv]

@[simp] theorem stepsFromHistory_historyFromSteps {n : ℕ}
    (T : ℕ) (y : Fin n) (steps : Fin T → Fin n) :
    stepsFromHistory T (historyFromSteps T y steps) = steps := by
  funext j
  simp [stepsFromHistory, historyFromSteps, Fin.cons_succ]

/-- Full inverse on exactly the histories with the prescribed starting
state. The initial coordinate is not an additional free random sample. -/
theorem historyFromSteps_stepsFromHistory {n : ℕ} (T : ℕ)
    (y : Fin n) (w : (i : Finset.Iic T) → Fin n)
    (hy : w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le T)⟩ = y) :
    historyFromSteps T y (stepsFromHistory T w) = w := by
  funext i
  let f : Fin (T+1) → Fin n := fun j => w ((historyTimeEquiv T).symm j)
  have hf : f 0 = y := by
    simpa [f, historyTimeEquiv] using hy
  have htail : Fin.cons (f 0) (Fin.tail f) = f :=
    Fin.cons_self_tail f
  have hs : stepsFromHistory T w = Fin.tail f := by
    funext j
    rfl
  have hi := congrFun htail (historyTimeEquiv T i)
  simpa [historyFromSteps, hs, f, hf] using hi

end ReverseSolver
end PermanssonResearch
