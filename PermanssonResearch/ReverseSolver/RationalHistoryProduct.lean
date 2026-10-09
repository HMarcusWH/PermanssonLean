import PermanssonResearch.ReverseSolver.AnchoredHistoryEquiv
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Tactic

/-!
# D0-C: exact rational products of chronological transition entries

Nonnegativity of every certified row entry ensures rational transition
products embed exactly into ENNReal, with no floating point approximation.
-/

namespace PermanssonResearch
namespace ReverseSolver

/-- The exact rational weight of the chronological transitions in a canonical
endpoint-inclusive finite history (the initial-point condition is separate). -/
def rationalHistoryWeight {n : ℕ}
    (M : RationalMarkovMatrix n) (T : ℕ)
    (w : (i : Finset.Iic T) → Fin n) : ℚ :=
  ∏ i : Fin T, M.entry
    (w ⟨i.val, Finset.mem_Iic.mpr (Nat.le_of_lt i.isLt)⟩)
    (w ⟨i.val+1, Finset.mem_Iic.mpr (Nat.succ_le_of_lt i.isLt)⟩)

theorem rationalHistoryWeight_nonneg {n : ℕ}
    (M : RationalMarkovMatrix n) (T : ℕ)
    (w : (i : Finset.Iic T) → Fin n) :
    0 ≤ rationalHistoryWeight M T w := by
  unfold rationalHistoryWeight
  exact Finset.prod_nonneg (fun i _ => M.entry_nonneg _ _)

/-- Exact identification of the rational and ENNReal finite transition
products, for every path and horizon, using certified nonnegative entries. -/
theorem canonicalHistoryWeight_eq_ofReal {n : ℕ}
    (M : RationalMarkovMatrix n) (T : ℕ)
    (w : (i : Finset.Iic T) → Fin n) :
    canonicalHistoryWeight M T w =
      ENNReal.ofReal ((rationalHistoryWeight M T w : ℚ) : ℝ) := by
  classical
  have hnonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin T)),
        0 ≤ (M.entry
          (w ⟨i.val, Finset.mem_Iic.mpr (Nat.le_of_lt i.isLt)⟩)
          (w ⟨i.val+1, Finset.mem_Iic.mpr
            (Nat.succ_le_of_lt i.isLt)⟩) : ℝ) := by
    intro i _
    exact_mod_cast M.entry_nonneg _ _
  have hprod := ENNReal.ofReal_prod_of_nonneg hnonneg
  unfold canonicalHistoryWeight rationalHistoryWeight
  rw [← hprod]
  congr 1
  norm_cast

end ReverseSolver
end PermanssonResearch
