import PermanssonResearch.ReverseSolver.ControlledKernelCorrespondence
import Mathlib.Tactic

/-!
# D1-A: state feedback succeeds when neither fixed control succeeds

States: 0=start, 1=bridge, 2=goal. False control: 0 -> 1, 1 -> 1.
True control: 0 -> 0, 1 -> 2. Both preserve goal state 2.

No fixed control reaches goal by T=2 starting at 0. A stationary state
feedback choice (false at 0, true at 1) reaches goal with probability one.
This is a genuinely state-dependent policy, NOT a time-indexed sequence of
arbitrary D0 FrozenMenu members. The underlying state-feedback process is
one Markov kernel; its typed world P and strategic update U remain fixed.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace ControlledKernelExamples

open ControlledKernel
open FiniteStrategicRealization
open FiniteStrategicPathBridge

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- A deterministic transition function as a certified rational matrix. -/
def deterministicMatrix {n : ℕ} (f : Fin n → Fin n) :
    RationalMarkovMatrix n where
  entry := fun y z => if z = f y then 1 else 0
  entry_nonneg := by
    intro y z
    split_ifs <;> norm_num
  row_sum_one := by
    intro y
    simp

/-- Left control moves from start to bridge but then gets stuck. -/
def leftStep (y : Fin 3) : Fin 3 :=
  if y = 0 then 1 else y

/-- Right control moves bridge to goal, but gets stuck at start. -/
def rightStep (y : Fin 3) : Fin 3 :=
  if y = 1 then 2 else y

def leftMatrix : RationalMarkovMatrix 3 := deterministicMatrix leftStep
def rightMatrix : RationalMarkovMatrix 3 := deterministicMatrix rightStep

/-- Both controls permitted everywhere, with nonempty eligible menu. -/
def toySystem : FiniteControlSystem Bool 3 where
  states_nonempty := by decide
  baseline := leftMatrix
  options := fun _ => {false, true}
  options_nonempty := by
    intro y
    exact ⟨false, by simp⟩
  matrix := fun c => if c then rightMatrix else leftMatrix

/-- Fully observed feedback: choose left at start, right thereafter. -/
def toyFeedback : StateFeedback toySystem where
  choose := fun y => if y = 0 then false else true
  permitted := by
    intro y
    simp [toySystem]

def alwaysLeft : StateFeedback toySystem :=
  constantFeedback toySystem false (by intro y; simp [toySystem])

def alwaysRight : StateFeedback toySystem :=
  constantFeedback toySystem true (by intro y; simp [toySystem])

def goalTwo : RationalHittingTarget 3 where
  goal := {2}
  forbidden := ∅
  disjoint := by simp

/-- Actual feedback kernel follows 0 -> 1 at the first transition. -/
theorem feedback_start_to_bridge :
    (feedbackMatrix toySystem toyFeedback).entry (0 : Fin 3) 1 = 1 := by
  norm_num [feedbackMatrix, toySystem, toyFeedback, leftMatrix,
    deterministicMatrix, leftStep]

/-- At the bridge the SAME feedback policy chooses the other control. -/
theorem feedback_bridge_to_goal :
    (feedbackMatrix toySystem toyFeedback).entry (1 : Fin 3) 2 = 1 := by
  norm_num [feedbackMatrix, toySystem, toyFeedback, rightMatrix,
    deterministicMatrix, rightStep]

/-- The feedback process hits the goal before two transitions have elapsed. -/
theorem feedback_value_two :
    rationalHittingValue (feedbackMatrix toySystem toyFeedback)
      goalTwo 2 (0 : Fin 3) = 1 := by
  norm_num [rationalHittingValue, Fin.sum_univ_three,
    feedbackMatrix, toySystem, toyFeedback, goalTwo,
    leftMatrix, rightMatrix, deterministicMatrix, leftStep, rightStep]

/-- Neither stationary fixed control reaches the goal from state 0 by T=2. -/
theorem any_fixed_control_zero (c : Bool) :
    rationalHittingValue (toySystem.matrix c)
      goalTwo 2 (0 : Fin 3) = 0 := by
  cases c <;>
    norm_num [rationalHittingValue, Fin.sum_univ_three,
      toySystem, goalTwo, leftMatrix, rightMatrix,
      deterministicMatrix, leftStep, rightStep]

theorem feedback_strictly_improves_on_any_fixed (c : Bool) :
    rationalHittingValue (toySystem.matrix c) goalTwo 2 (0 : Fin 3) <
      rationalHittingValue (feedbackMatrix toySystem toyFeedback)
        goalTwo 2 (0 : Fin 3) := by
  rw [any_fixed_control_zero c, feedback_value_two]
  norm_num

/-- The improvement also holds for the actual canonical typed prefix-event
probabilities, rather than only an abstract matrix calculation. -/
theorem typed_feedback_value_two :
    hittingValue (typedTarget goalTwo)
      (feedbackModel toySystem toyFeedback).inducedKernel
      (decode (0 : Fin 3)) 2 = 1 := by
  rw [feedback_typed_hitting_value]
  rw [feedback_value_two]
  norm_num

theorem typed_fixed_value_zero (c : Bool) :
    hittingValue (typedTarget goalTwo)
      (realizedModel (toySystem.matrix c)).inducedKernel
      (decode (0 : Fin 3)) 2 = 0 := by
  rw [typedHittingValue_eq_rational_all_horizons]
  rw [any_fixed_control_zero c]
  norm_num

theorem typed_feedback_strictly_improves (c : Bool) :
    hittingValue (typedTarget goalTwo)
      (realizedModel (toySystem.matrix c)).inducedKernel
        (decode (0 : Fin 3)) 2 <
    hittingValue (typedTarget goalTwo)
      (feedbackModel toySystem toyFeedback).inducedKernel
        (decode (0 : Fin 3)) 2 := by
  rw [typed_fixed_value_zero, typed_feedback_value_two]
  norm_num

/-- No policy-selection trick changes the original world P or update U. -/
theorem example_preserves_world :
    (feedbackModel toySystem toyFeedback).world =
      (realizedModel toySystem.baseline).world :=
  feedback_preserves_world toySystem toyFeedback

theorem example_preserves_update :
    (feedbackModel toySystem toyFeedback).generator.update =
      (realizedModel toySystem.baseline).generator.update :=
  feedback_preserves_update toySystem toyFeedback

end ControlledKernelExamples
end ReverseSolver
end PermanssonResearch
