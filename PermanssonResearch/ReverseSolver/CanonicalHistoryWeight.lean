import PermanssonResearch.ReverseSolver.CanonicalEventSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# D0-C: canonical atomic history masses as exact transition products

Each historical path carries its exact product of certified one-step
probabilities. The initial state is constrained to the fixed start.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver

/-- The exact product of transition probabilities along an indexed history.
The product is empty (and therefore one) at horizon zero. -/
noncomputable def canonicalHistoryWeight {n : ℕ}
    (M : RationalMarkovMatrix n) (T : ℕ)
    (w : ((i : Finset.Iic T) → Fin n)) : ℝ≥0∞ :=
  ∏ i : Fin T, ENNReal.ofReal
    (M.entry
      (w ⟨i.val, Finset.mem_Iic.mpr (Nat.le_of_lt i.isLt)⟩)
      (w ⟨i.val+1, Finset.mem_Iic.mpr (Nat.succ_le_of_lt i.isLt)⟩) : ℝ)

@[simp] theorem canonicalHistoryWeight_zero {n : ℕ}
    (M : RationalMarkovMatrix n)
    (w : ((i : Finset.Iic 0) → Fin n)) :
    canonicalHistoryWeight M 0 w = 1 := by
  simp [canonicalHistoryWeight]

/-- Appending the next state multiplies the prefix product by exactly
the last transition entry, for every finite history. -/
theorem canonicalHistoryWeight_succ {n : ℕ}
    (M : RationalMarkovMatrix n) (T : ℕ)
    (w : ((i : Finset.Iic (T+1)) → Fin n)) :
    canonicalHistoryWeight M (T+1) w =
      canonicalHistoryWeight M T
        (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) T.le_succ w) *
      ENNReal.ofReal (M.entry
        (w ⟨T, Finset.mem_Iic.mpr T.le_succ⟩)
        (w ⟨T+1, Finset.mem_Iic.mpr le_rfl⟩) : ℝ) := by
  classical
  unfold canonicalHistoryWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rfl
  · rfl

end ReverseSolver
end PermanssonResearch
