import PermanssonResearch.ReverseSolver.BellmanOptimality
import PermanssonResearch.ReverseSolver.ControlledKernelExamples
import Mathlib.Tactic

/-!
# D1-B rational regression witnesses and policy-class separation

The first witness transports D1-A's genuine canonical stationary feedback
example. The new three-state example has probe, goal, and forbidden states:
probe succeeds with probability 1/4 or stays with probability 3/4;
gamble succeeds with probability 1/2 or fails with probability 1/2.
At horizon two, a deadline-dependent policy probes first and gambles if
still at the start: exact value 5/8. Each deterministic stationary policy
has value at most 1/2, even allowing choices depending on the state.

These are claims about the rational recursive policy evaluator.
A nonstationary canonical path-law construction is reserved for D1-C.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace BellmanExamples

open Bellman
open ControlledKernel
open ControlledKernelExamples

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- Probe: from 0 go to goal 1 with chance 1/4, otherwise stay at 0. -/
def probeMatrix : RationalMarkovMatrix 3 where
  entry := fun y z =>
    if y = 0 then
      if z = 0 then 3/4 else if z = 1 then 1/4 else 0
    else if z = y then 1 else 0
  entry_nonneg := by
    intro y z
    split_ifs <;> norm_num
  row_sum_one := by
    intro y
    fin_cases y <;> norm_num [Fin.sum_univ_three]

/-- Gamble: from 0 go to goal 1 with chance 1/2 or danger 2 with chance 1/2. -/
def gambleMatrix : RationalMarkovMatrix 3 where
  entry := fun y z =>
    if y = 0 then
      if z = 1 then 1/2 else if z = 2 then 1/2 else 0
    else if z = y then 1 else 0
  entry_nonneg := by
    intro y z
    split_ifs <;> norm_num
  row_sum_one := by
    intro y
    fin_cases y <;> norm_num [Fin.sum_univ_three]

def deadlineSystem : FiniteControlSystem Bool 3 where
  states_nonempty := by decide
  baseline := probeMatrix
  options := fun _ => {false, true}
  options_nonempty := by
    intro y
    exact ⟨false, by simp⟩
  matrix := fun c => if c then gambleMatrix else probeMatrix

def deadlineTarget : RationalHittingTarget 3 where
  goal := {1}
  forbidden := {2}
  disjoint := by simp

/-- At two transitions remaining, probe. At one transition remaining,
gamble. Both controls are eligible at all states. -/
def deadlineSchedule : MarkovSchedule deadlineSystem :=
  fun remaining => {
    choose := fun _ => if remaining = 2 then false else true
    permitted := by
      intro y
      by_cases h : remaining = 2
      · simp [deadlineSystem, h]
      · simp [deadlineSystem, h]
  }

/-- The exact deadline-aware policy value is 5/8, not a floating estimate. -/
theorem deadline_policy_five_eighths :
    policyValue deadlineSystem deadlineTarget deadlineSchedule 2 (0 : Fin 3) =
      5 / 8 := by
  norm_num [policyValue, actionScore, deadlineSystem, deadlineTarget,
    deadlineSchedule, probeMatrix, gambleMatrix, Fin.sum_univ_three]

/-- Every deterministic stationary feedback has at most two possibilities
at the start state, even if it chooses controls differently elsewhere.
The goal and danger are evaluation-terminal. -/
theorem stationary_deadline_value_cases (π : StateFeedback deadlineSystem) :
    policyValue deadlineSystem deadlineTarget (stationarySchedule π)
        2 (0 : Fin 3) = 7/16 ∨
    policyValue deadlineSystem deadlineTarget (stationarySchedule π)
        2 (0 : Fin 3) = 1/2 := by
  cases h : π.choose (0 : Fin 3) with
  | false =>
      left
      norm_num [policyValue, actionScore, stationarySchedule,
        deadlineSystem, deadlineTarget, probeMatrix, gambleMatrix,
        Fin.sum_univ_three, h]
  | true =>
      right
      norm_num [policyValue, actionScore, stationarySchedule,
        deadlineSystem, deadlineTarget, probeMatrix, gambleMatrix,
        Fin.sum_univ_three, h]

/-- Strong separation against ALL deterministic stationary policies,
not just the two globally constant control selections. -/
theorem deadline_beats_every_deterministic_stationary
    (π : StateFeedback deadlineSystem) :
    policyValue deadlineSystem deadlineTarget (stationarySchedule π)
        2 (0 : Fin 3) <
      policyValue deadlineSystem deadlineTarget deadlineSchedule 2
        (0 : Fin 3) := by
  rcases stationary_deadline_value_cases π with h | h
  · rw [h, deadline_policy_five_eighths]
    norm_num
  · rw [h, deadline_policy_five_eighths]
    norm_num

/-- The Bellman value dominates the concrete deadline-dependent policy. -/
theorem deadline_policy_bounded_by_bellman :
    (5/8 : ℚ) ≤ bellmanValue deadlineSystem deadlineTarget 2 (0 : Fin 3) := by
  rw [← deadline_policy_five_eighths]
  exact policyValue_le_bellman deadlineSystem deadlineTarget deadlineSchedule
    2 (0 : Fin 3)

/-- A stationary controller from D1-A retains exactly its genuine canonical
typed hitting probability, independent of the new optimization proof. -/
theorem prior_feedback_bridge :
    (policyValue toySystem goalTwo
      (stationarySchedule toyFeedback) 2 (0 : Fin 3) : ℝ) =
    hittingValue (FiniteStrategicPathBridge.typedTarget goalTwo)
      (feedbackModel toySystem toyFeedback).inducedKernel
      (FiniteStrategicRealization.decode (0 : Fin 3)) 2 :=
  stationarySchedule_value_eq_typed toySystem goalTwo toyFeedback 0 2

/-- An explicitly nonempty goal can be impossible: both available controls
leave state 0 unchanged, although goal state 1 exists. -/
def unreachableSystem : FiniteControlSystem Bool 2 where
  states_nonempty := by decide
  baseline := deterministicMatrix id
  options := fun _ => {false, true}
  options_nonempty := by
    intro y
    exact ⟨false, by simp⟩
  matrix := fun _ => deterministicMatrix id

def unreachableTarget : RationalHittingTarget 2 where
  goal := {1}
  forbidden := ∅
  disjoint := by simp

theorem unreachable_target_nonempty : unreachableTarget.goal.Nonempty := by
  simp [unreachableTarget]

theorem unreachable_goal_zero :
    ∀ (t : ℕ), bellmanValue unreachableSystem unreachableTarget t
      (0 : Fin 2) = 0 := by
  intro t
  induction t with
  | zero =>
      norm_num [bellmanValue_zero, unreachableTarget]
  | succ t ih =>
      rw [bellmanValue_succ]
      have hg : (0 : Fin 2) ∉ unreachableTarget.goal := by
        simp [unreachableTarget]
      have hd : (0 : Fin 2) ∉ unreachableTarget.forbidden := by
        simp [unreachableTarget]
      simp only [if_neg hg, if_neg hd]
      change (∑ z : Fin 2,
        (if z = (0 : Fin 2) then (1 : ℚ) else 0) *
          bellmanValue unreachableSystem unreachableTarget t z) = 0
      simpa [Fin.sum_univ_two] using ih

end BellmanExamples
end ReverseSolver
end PermanssonResearch
