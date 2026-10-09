import PermanssonResearch.ReverseSolver.CanonicalWordEncoding
import Mathlib.Tactic

/-!
# D0-C: anchored-history/successor-word bijection

No finite-prefix history coordinate may be sampled before the initial y.
There is an explicit equivalence between T successor-state vectors and the
histories of length T+1 that have the mandated initial coordinate.
-/

namespace PermanssonResearch
namespace ReverseSolver

/-- A genuine finite history conditioned on having the prescribed first
coordinate, rather than an unconstrained independent initial draw. -/
def anchoredHistory {n : ℕ} (T : ℕ) (y : Fin n) :=
  {w : ((i : Finset.Iic T) → Fin n) //
    w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le T)⟩ = y}

/-- Canonical paths with a fixed initial state are exactly T successive
states; this is a bijection, not a surjective approximation. -/
def anchoredHistoryEquiv {n : ℕ} (T : ℕ) (y : Fin n) :
    (Fin T → Fin n) ≃ anchoredHistory T y where
  toFun v := ⟨historyFromSteps T y v, historyFromSteps_initial T y v⟩
  invFun w := stepsFromHistory T w.1
  left_inv v := stepsFromHistory_historyFromSteps T y v
  right_inv w := by
    apply Subtype.ext
    exact historyFromSteps_stepsFromHistory T y w.1 w.property

end ReverseSolver
end PermanssonResearch
