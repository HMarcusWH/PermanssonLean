import PermanssonResearch.ReverseSolver.CanonicalHistoryWeight
import Mathlib.Tactic

/-!
# D0-C: exact atomic probabilities for *every* canonical history

A canonical point-started finite history has zero mass if it starts at the
wrong state, and otherwise has exactly the product of its rational transitions.
This establishes the bridge at the level of each individual path atom;
the event-sum/word-enumeration transport is still separate.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver

private theorem singletonHistory_eq_of_initial {n : ℕ}
    (y : Fin n) (w : (i : Finset.Iic 0) → Fin n)
    (h : w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩ = y) :
    w = PermanssonLean.ProbabilitySupport.singletonPrefix y := by
  funext i
  have hi : i = ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩ := by
    apply Subtype.ext
    exact Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property)
  rw [hi]
  simpa [PermanssonLean.ProbabilitySupport.singletonPrefix] using h

/-- Strong all-horizon atom formula: the real canonical Markov history law
agrees *atom by atom* with the exact certified matrix transition product.
Incorrect initial states have probability zero. -/
theorem rationalFiniteKernel_prefix_atom_product {n : ℕ}
    (M : RationalMarkovMatrix n) (y : Fin n) :
    ∀ (T : ℕ) (w : (i : Finset.Iic T) → Fin n),
      PermanssonLean.ProbabilitySupport.finitePrefixLaw
        (rationalFiniteKernel M) y T {w} =
        if w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le T)⟩ = y then
          canonicalHistoryWeight M T w
        else 0 := by
  intro T
  induction T with
  | zero =>
      intro w
      rw [rationalFiniteKernel_prefix_zero]
      rw [Measure.dirac_apply' _ (measurableSet_singleton w)]
      by_cases hy : w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩ = y
      · have hw := singletonHistory_eq_of_initial y w hy
        simp [canonicalHistoryWeight, hy, hw,
          PermanssonLean.ProbabilitySupport.singletonPrefix]
      · have hw : PermanssonLean.ProbabilitySupport.singletonPrefix y ≠ w := by
          intro hh
          apply hy
          have hh0 := congrFun hh ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩
          simpa [PermanssonLean.ProbabilitySupport.singletonPrefix] using hh0.symm
        simp [canonicalHistoryWeight, hy, hw]
  | succ T ih =>
      intro w
      rw [rationalFiniteKernel_prefix_singleton_succ M y T w]
      rw [ih (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n) T.le_succ w)]
      rw [canonicalHistoryWeight_succ]
      have hzero :
          (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin n)
            T.le_succ w)
              ⟨0, Finset.mem_Iic.mpr (Nat.zero_le T)⟩ =
          w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le (T+1))⟩ := rfl
      rw [hzero]
      by_cases hy :
          w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le (T+1))⟩ = y
      · simp [hy]
      · simp [hy]

end ReverseSolver
end PermanssonResearch
