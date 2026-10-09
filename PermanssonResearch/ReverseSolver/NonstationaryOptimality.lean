import PermanssonResearch.ReverseSolver.NonstationaryForward
import PermanssonResearch.ReverseSolver.CanonicalFiniteEventSum
import Mathlib.Tactic

/-!
# D1-C1: actual nonstationary success-event probability = policyValue

This is a two-sided proof. The genuine Ionescu--Tulcea partialTraj law
is independently reduced to exact rational path products. An independent
forward enumeration of all successor lists is proved to satisfy Bellman's
policy recursion. A full-history bijection then identifies the results.

This is RATIONAL finite-world nonstationary probability semantics only.
Typed alpha/P/U nonstationary transport belongs to D1-C2 (#48).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace Nonstationary

open Bellman
open ControlledKernel

universe uC

/-- Reindex every full history by its genuine initial point and successor
vector; only the fixed initial point survives. This is exact finite
enumeration with no missing paths and no phantom initial transition. -/
theorem successfulPathSum_eq_forwardEnumeration
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (target : RationalHittingTarget n) (T : ℕ) (x : Fin n) :
    successfulPathSum sys π target T x =
      forwardEnumeration sys π target T x := by
  classical
  let E := successPrefixEvent (rationalTargetAsFrozen target) T
  unfold successfulPathSum
  calc
    (∑ w : ((i : Finset.Iic T) → Fin n),
        if w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le T)⟩ = x ∧
           w ∈ E then rationalPathWeight sys π T T w else 0) =
      ∑ p : Fin n × (Fin T → Fin n),
        if (historyFromSteps T p.1 p.2)
            ⟨0, Finset.mem_Iic.mpr (Nat.zero_le T)⟩ = x ∧
           historyFromSteps T p.1 p.2 ∈ E then
          rationalPathWeight sys π T T
            (historyFromSteps T p.1 p.2)
        else 0 := by
          symm
          apply Fintype.sum_equiv (fullHistoryEquiv (n := n) T)
          intro p
          rfl
    _ = ∑ v : Fin T → Fin n,
        if historyFromSteps T x v ∈ E then
          rationalPathWeight sys π T T (historyFromSteps T x v)
        else 0 := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v hv
          simp only [historyFromSteps_initial]
          calc
            (∑ a : Fin n,
                if a = x ∧ historyFromSteps T a v ∈ E then
                  rationalPathWeight sys π T T (historyFromSteps T a v)
                else 0) =
              (∑ a : Fin n,
                if a = x then
                  (if historyFromSteps T a v ∈ E then
                    rationalPathWeight sys π T T (historyFromSteps T a v)
                  else 0)
                else 0) := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  by_cases h : a = x <;> simp [h]
            _ = (if historyFromSteps T x v ∈ E then
                  rationalPathWeight sys π T T (historyFromSteps T x v)
                 else 0) := by simp
    _ = ∑ v : Fin T → Fin n,
        if successorWordWins target x (List.ofFn v) then
          rationalPathWeight sys π T T (historyFromSteps T x v)
        else 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          exact if_congr (canonicalSuccess_iff_wordWins target T x v) rfl rfl
    _ = ∑ v : Fin T → Fin n,
        remainingWordMass sys π T x (List.ofFn v) *
          (if successorWordWins target x (List.ofFn v) then
            (1 : ℚ) else 0) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [remainingWordMass_ofFn_eq_pathWeight sys π T x v]
          split_ifs <;> simp
    _ = forwardEnumeration sys π target T x := by
          unfold forwardEnumeration
          exact (finiteSuccessorWords_sum_eq_vectorSum n T
            (fun xs => remainingWordMass sys π T x xs *
              (if successorWordWins target x xs then
                (1 : ℚ) else 0))).symm

/-- Decisive D1-C1 theorem. The REAL probability of the ORIGINAL first-goal
before-forbidden event under the true time-indexed partialTraj law equals
the exact rational D1-B policyValue, at every state and finite deadline. -/
theorem successProbability_eq_policyValue
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (target : RationalHittingTarget n) (T : ℕ) (x : Fin n) :
    successProbability sys π target T x =
      ENNReal.ofReal ((policyValue sys target π T x : ℚ) : ℝ) := by
  rw [successProbability_eq_rationalPathSum,
    successfulPathSum_eq_forwardEnumeration,
    forwardEnumeration_eq_policyValue]

/-- Probabilistic Bellman upper bound for every declared admissible
deterministic time-dependent Markov policy, as genuine event masses. -/
theorem successProbability_le_bellman
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (target : RationalHittingTarget n) (T : ℕ) (x : Fin n) :
    successProbability sys π target T x ≤
      ENNReal.ofReal ((bellmanValue sys target T x : ℚ) : ℝ) := by
  rw [successProbability_eq_policyValue]
  apply ENNReal.ofReal_le_ofReal
  exact_mod_cast policyValue_le_bellman sys target π T x

/-- The D1-B maximizing schedule reaches the true Bellman upper bound
under the real nonstationary finite-horizon path measure. -/
theorem maximizingSchedule_actual_probability
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) (T : ℕ) (x : Fin n) :
    successProbability sys (maximizingSchedule sys target) target T x =
      ENNReal.ofReal ((bellmanValue sys target T x : ℚ) : ℝ) := by
  rw [successProbability_eq_policyValue,
    maximizingSchedule_attains]

end Nonstationary
end ReverseSolver
end PermanssonResearch
