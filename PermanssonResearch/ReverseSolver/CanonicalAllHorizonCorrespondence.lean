import PermanssonResearch.ReverseSolver.CanonicalFiniteEventSum
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Tactic

/-!
# D0-C: unconditional finite-horizon canonical/rational correspondence

The actual mathlib finitePrefixLaw probability of the literal frozen
successPrefixEvent is equal to the original D0-B rational forward
enumeration, hence to its independently established backward recurrence.
No correspondence assumption is taken as an input.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver

/-- Reindex the original D0-B word enumeration by exact successor vectors,
then replace its recursive word mass by the certified rational path product. -/
theorem rationalForwardEnumeration_eq_vector_weight_sum {n : ℕ}
    (M : RationalMarkovMatrix n) (target : RationalHittingTarget n)
    (T : ℕ) (y : Fin n) :
    rationalForwardEnumeration M target T y =
    ∑ v : Fin T → Fin n,
      if successorWordWins target y (List.ofFn v) then
        rationalHistoryWeight M T (historyFromSteps T y v)
      else 0 := by
  classical
  unfold rationalForwardEnumeration
  rw [finiteSuccessorWords_sum_eq_vectorSum]
  apply Finset.sum_congr rfl
  intro v _
  rw [successorWordMass_ofFn_eq_rationalHistoryWeight M T y v]
  cases h : successorWordWins target y (List.ofFn v) <;> simp [h]

/-- Exact all-horizon equality in ENNReal: the original forward rational
enumerator is the probability of the actual canonical success event. -/
theorem rationalFiniteKernel_success_eq_forward_ofReal {n : ℕ}
    (M : RationalMarkovMatrix n) (target : RationalHittingTarget n)
    (T : ℕ) (y : Fin n) :
    PermanssonLean.ProbabilitySupport.finitePrefixLaw
      (rationalFiniteKernel M) y T
      (successPrefixEvent (rationalTargetAsFrozen target) T) =
    ENNReal.ofReal ((rationalForwardEnumeration M target T y : ℚ) : ℝ) := by
  classical
  rw [rationalFiniteKernel_success_eq_vector_weight_sum]
  let q (v : Fin T → Fin n) : ℚ :=
    if successorWordWins target y (List.ofFn v) then
      rationalHistoryWeight M T (historyFromSteps T y v) else 0
  have hterm (v : Fin T → Fin n) :
      (if successorWordWins target y (List.ofFn v) then
        canonicalHistoryWeight M T (historyFromSteps T y v) else 0) =
      ENNReal.ofReal ((q v : ℚ) : ℝ) := by
    dsimp [q]
    cases h : successorWordWins target y (List.ofFn v) <;>
      simp [h, canonicalHistoryWeight_eq_ofReal]
  simp_rw [hterm]
  have hnonneg : ∀ v ∈ (Finset.univ : Finset (Fin T → Fin n)),
      0 ≤ ((q v : ℚ) : ℝ) := by
    intro v _
    dsimp [q]
    split_ifs
    · exact_mod_cast rationalHistoryWeight_nonneg M T (historyFromSteps T y v)
    · norm_num
  rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]
  congr 1
  have hq : (∑ v : Fin T → Fin n, q v) =
      rationalForwardEnumeration M target T y := by
    simpa [q] using (rationalForwardEnumeration_eq_vector_weight_sum M target T y).symm
  exact_mod_cast hq

/-- D0-C: the certified rational hitting value is exactly the hitting
probability in the genuine canonical mathlib finite-prefix Markov law at
EVERY finite horizon. No extra correspondence or strategic-world hypothesis. -/
theorem rationalHittingValue_eq_canonical_all_horizons {n : ℕ}
    (M : RationalMarkovMatrix n) (target : RationalHittingTarget n)
    (T : ℕ) (y : Fin n) :
    (rationalHittingValue M target T y : ℝ) =
      hittingValue (rationalTargetAsFrozen target)
        (rationalFiniteKernel M) y T := by
  have hforward := rationalForwardEnumeration_eq_recursion M target T y
  have hnonneg : 0 ≤ ((rationalForwardEnumeration M target T y : ℚ) : ℝ) := by
    rw [hforward]
    exact_mod_cast (rationalHittingValue_mem_Icc M target T y).1
  unfold hittingValue Measure.real
  rw [rationalFiniteKernel_success_eq_forward_ofReal]
  rw [ENNReal.toReal_ofReal hnonneg]
  exact congrArg (fun q : ℚ => (q : ℝ)) hforward.symm

end ReverseSolver
end PermanssonResearch
