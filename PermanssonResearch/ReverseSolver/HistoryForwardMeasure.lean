import PermanssonResearch.ReverseSolver.HistoryForwardBridge
import PermanssonResearch.ReverseSolver.HistoryBellmanDominance
import Mathlib.Tactic

/-!
# D1-D1: universal history-policy dominance over the ACTUAL first-hit law

The exact-rational forward continuation enumerator is equated with the
unchanged D0 first-target-before-forbidden event under the genuine Mathlib
partialTraj measure. The independent backwards Bellman induction then bounds
ALL admissible deterministic complete-history policies; the certified D1-B
maximizing schedule attains that bound via the exact Markov embedding.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependent

open Bellman ControlledKernel
open PermanssonLean.ProbabilitySupport
universe uC

/-- Exactly reindex the true successful full-history rational path sum as
an independent exhaustive successor-word calculation, without inventing
any extra time-zero samples or altering the first-hit event. -/
theorem successfulPathSum_eq_forwardValue
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    successfulPathSum sys σ target D x =
      forwardValue sys σ target D 0 (singletonPrefix x)
        (initialStatus target x) D := by
  classical
  let E := successPrefixEvent (rationalTargetAsFrozen target) D
  unfold successfulPathSum
  calc
    (∑ w : History n D,
      if w ⟨0, Finset.mem_Iic.mpr (Nat.zero_le D)⟩ = x ∧ w ∈ E
      then rationalPathWeight sys σ D D w else 0) =
      ∑ p : Fin n × (Fin D → Fin n),
        if (historyFromSteps D p.1 p.2)
            ⟨0, Finset.mem_Iic.mpr (Nat.zero_le D)⟩ = x ∧
           historyFromSteps D p.1 p.2 ∈ E then
          rationalPathWeight sys σ D D
            (historyFromSteps D p.1 p.2)
        else 0 := by
          symm
          apply Fintype.sum_equiv (fullHistoryEquiv (n := n) D)
          intro p
          rfl
    _ = ∑ v : Fin D → Fin n,
        if historyFromSteps D x v ∈ E then
          rationalPathWeight sys σ D D (historyFromSteps D x v)
        else 0 := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v hv
          simp only [historyFromSteps_initial]
          calc
            (∑ a : Fin n,
              if a = x ∧ historyFromSteps D a v ∈ E then
                rationalPathWeight sys σ D D (historyFromSteps D a v)
              else 0) =
              ∑ a : Fin n,
                if a = x then
                  (if historyFromSteps D a v ∈ E then
                    rationalPathWeight sys σ D D (historyFromSteps D a v)
                  else 0)
                else 0 := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  by_cases h : a = x <;> simp [h]
            _ = (if historyFromSteps D x v ∈ E then
                  rationalPathWeight sys σ D D (historyFromSteps D x v)
                 else 0) := by simp
    _ = ∑ v : Fin D → Fin n,
          completionMass sys σ D 0 (singletonPrefix x) (List.ofFn v) *
            (if (List.ofFn v).foldl (advanceStatus target)
                  (initialStatus target x) = .won then (1 : ℚ) else 0) := by
          apply Finset.sum_congr rfl
          intro v _
          have hmass := completionMass_eq_rationalPathWeight sys σ D D
            (historyFromSteps D x v)
          have hmass' : completionMass sys σ D 0 (singletonPrefix x)
              (List.ofFn v) =
              rationalPathWeight sys σ D D (historyFromSteps D x v) := by
            simpa using hmass
          have hstatus := foldl_status_won_iff_successPrefixEvent target D
            (historyFromSteps D x v)
          have hstatus' :
              ((List.ofFn v).foldl (advanceStatus target)
                (initialStatus target x) = .won) ↔
              historyFromSteps D x v ∈ E := by
            simpa [E] using hstatus
          by_cases he : historyFromSteps D x v ∈ E
          · have hw := hstatus'.mpr he
            simp [he, hw, hmass']
          · have hw : ¬ ((List.ofFn v).foldl (advanceStatus target)
                  (initialStatus target x) = .won) := by
              exact fun hh => he (hstatus'.mp hh)
            simp [he, hw]
    _ = forwardValue sys σ target D 0 (singletonPrefix x)
          (initialStatus target x) D := by
          unfold forwardValue
          exact (finiteSuccessorWords_sum_eq_vectorSum n D
            (fun xs => completionMass sys σ D 0 (singletonPrefix x) xs *
              (if xs.foldl (advanceStatus target) (initialStatus target x) = .won
                then (1 : ℚ) else 0))).symm

/-- Decisive exact correspondence: a genuine history-dependent first-hit
EVENT probability equals the separately evaluated rational continuation. -/
theorem successProbability_eq_forwardValue
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    successProbability sys σ target D x =
      ENNReal.ofReal ((forwardValue sys σ target D 0
        (singletonPrefix x) (initialStatus target x) D : ℚ) : ℝ) := by
  rw [successProbability_eq_rationalPathSum,
    successfulPathSum_eq_forwardValue]

/-- Every admissible deterministic complete-history policy is dominated by
D1-B's exact Bellman value UNDER THE REAL partialTraj event law. -/
theorem successProbability_le_bellman
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    successProbability sys σ target D x ≤
      ENNReal.ofReal ((bellmanValue sys target D x : ℚ) : ℝ) := by
  rw [successProbability_eq_forwardValue]
  apply ENNReal.ofReal_le_ofReal
  exact_mod_cast forwardValue_initial_le_bellman sys σ target D x

/-- Complete finite-horizon Markov sufficiency: every deterministic
history controller obeys Bellman's bound and an embedded original D1-B
maximizer attains it. No arbitrary path-law equivalence is claimed. -/
theorem history_bellman_optimal_and_attained
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    (∀ σ : HistoryPolicy sys,
      successProbability sys σ target D x ≤
        ENNReal.ofReal ((bellmanValue sys target D x : ℚ) : ℝ)) ∧
    (∃ σ : HistoryPolicy sys,
      successProbability sys σ target D x =
        ENNReal.ofReal ((bellmanValue sys target D x : ℚ) : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro σ
    exact successProbability_le_bellman sys σ target D x
  · exact ⟨embedMarkov sys (maximizingSchedule sys target),
      embedded_maximizingSchedule_attains sys target D x⟩

end HistoryDependent
end ReverseSolver
end PermanssonResearch
