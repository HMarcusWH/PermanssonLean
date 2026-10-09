import PermanssonResearch.ReverseSolver.NonstationaryPathAtoms
import PermanssonResearch.ReverseSolver.CanonicalWordEvent
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Tactic

/-!
# D1-C1: exact probability of the genuine first-hit event

No new hitting event is invented: the original measurable
successPrefixEvent is evaluated against the true nonstationary
Mathlib partialTraj measure. Finite atom additivity gives the exact
rational full-history sum of goal-before-forbidden successes.
The independent first-successor recursion comparison to policyValue
is a later theorem obligation, not a definition.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace Nonstationary

open Bellman
open ControlledKernel

universe uC

/-- The genuine nonstationary success event probability. -/
noncomputable def successProbability {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (target : RationalHittingTarget n) (T : ℕ) (x : Fin n) : ℝ≥0∞ :=
  prefixLaw sys π T x T
    (successPrefixEvent (rationalTargetAsFrozen target) T)

/-- Exact rational finite sum of ALL successful paths, with initial
coordinate constrained to the actual initial point (no phantom start). -/
def successfulPathSum {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (target : RationalHittingTarget n) (T : ℕ) (x : Fin n) : ℚ :=
  ∑ w : ((i : Finset.Iic T) → Fin n),
    if w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le T)⟩ = x ∧
       w ∈ successPrefixEvent (rationalTargetAsFrozen target) T then
      rationalPathWeight sys π T T w
    else 0

theorem successfulPathSum_nonneg {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (target : RationalHittingTarget n) (T : ℕ) (x : Fin n) :
    0 ≤ successfulPathSum sys π target T x := by
  unfold successfulPathSum
  apply Finset.sum_nonneg
  intro w hw
  split_ifs
  · exact rationalPathWeight_nonneg sys π T T w
  · norm_num

/-- The actual canonical event probability equals the full-history
rational sum, embedded with exact ENNReal conversion. No approximation. -/
theorem successProbability_eq_rationalPathSum
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (target : RationalHittingTarget n) (T : ℕ) (x : Fin n) :
    successProbability sys π target T x =
      ENNReal.ofReal ((successfulPathSum sys π target T x : ℚ) : ℝ) := by
  classical
  let μ := prefixLaw sys π T x T
  let E := successPrefixEvent (rationalTargetAsFrozen target) T
  have hfilter :
      (↑(Finset.univ.filter
        (fun w : ((i : Finset.Iic T) → Fin n) => w ∈ E)) :
          Set ((i : Finset.Iic T) → Fin n)) = E := by
    ext w
    simp
  change μ E = ENNReal.ofReal ((successfulPathSum sys π target T x : ℚ) : ℝ)
  calc
    μ E = μ (↑(Finset.univ.filter
      (fun w : ((i : Finset.Iic T) → Fin n) => w ∈ E)) :
        Set ((i : Finset.Iic T) → Fin n)) := by rw [hfilter]
    _ = ∑ w ∈ Finset.univ.filter
        (fun w : ((i : Finset.Iic T) → Fin n) => w ∈ E),
        μ {w} := by rw [sum_measure_singleton]
    _ = ∑ w : ((i : Finset.Iic T) → Fin n),
        if w ∈ E then μ {w} else 0 := by
          simp [Finset.sum_filter]
    _ = ∑ w : ((i : Finset.Iic T) → Fin n),
        ENNReal.ofReal ((if w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le T)⟩ = x ∧
          w ∈ E then rationalPathWeight sys π T T w else 0 : ℚ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [prefix_atom_product sys π T x T w]
          by_cases hs : w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le T)⟩ = x
          · by_cases he : w ∈ E <;> simp [hs, he]
          · simp [hs]
    _ = ENNReal.ofReal ((successfulPathSum sys π target T x : ℚ) : ℝ) := by
          have hnonneg : ∀ w ∈
                (Finset.univ : Finset ((i : Finset.Iic T) → Fin n)),
                0 ≤ ((if w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le T)⟩ = x ∧
                  w ∈ E then rationalPathWeight sys π T T w else 0 : ℚ) : ℝ) := by
              intro w hw
              split_ifs
              · exact_mod_cast rationalPathWeight_nonneg sys π T T w
              · norm_num
          rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]
          unfold successfulPathSum
          rfl

end Nonstationary
end ReverseSolver
end PermanssonResearch
