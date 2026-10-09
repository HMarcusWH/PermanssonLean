import PermanssonResearch.ReverseSolver.Bellman
import PermanssonResearch.ReverseSolver.ControlledKernelCorrespondence
import Mathlib.Tactic

/-!
# D1-B: exact recursive evaluation of deterministic Markov schedules

A schedule chooses an admissible state-feedback rule at each number of
REMAINING transitions. The choice at a horizon t+1 is applied BEFORE one
transition; the continuation has t transitions remaining. This is an
algebraic evaluator, not yet a proved nonstationary canonical path law.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace Bellman

open ControlledKernel
open FiniteStrategicPathBridge

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

universe uC

/-- One admissible state-feedback rule for each remaining-horizon index. -/
abbrev MarkovSchedule {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) := ℕ → StateFeedback sys

/-- The same STATE-FEEDBACK selector at all remaining horizons.
Unlike D1-A constantFeedback, it need not select one global constant control. -/
def stationarySchedule {C : Type uC} [DecidableEq C] {n : ℕ}
    {sys : FiniteControlSystem C n} (π : StateFeedback sys) :
    MarkovSchedule sys := fun _ => π

/-- Recursive success value of a deterministic time-dependent policy. This
function does NOT assert equivalence to a nonstationary finite-prefix law. -/
def policyValue {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) (π : MarkovSchedule sys) :
    ℕ → Fin n → ℚ
  | 0, y => if y ∈ target.goal then 1 else 0
  | t + 1, y =>
      if y ∈ target.goal then 1
      else if y ∈ target.forbidden then 0
      else actionScore sys (policyValue sys target π t) y
        ((π (t+1)).choose y)

@[simp] theorem policyValue_zero {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) (π : MarkovSchedule sys)
    (y : Fin n) :
    policyValue sys target π 0 y =
      if y ∈ target.goal then 1 else 0 := rfl

theorem policyValue_succ {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) (π : MarkovSchedule sys)
    (t : ℕ) (y : Fin n) :
    policyValue sys target π (t+1) y =
      if y ∈ target.goal then 1
      else if y ∈ target.forbidden then 0
      else actionScore sys (policyValue sys target π t) y
        ((π (t+1)).choose y) := rfl

/-- A stationary schedule's recursion is precisely D1-A's frozen
state-feedback rational hitting recursion at EVERY horizon and initial state. -/
theorem stationarySchedule_value_eq_rational
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) (π : StateFeedback sys) :
    ∀ (t : ℕ) (y : Fin n),
      policyValue sys target (stationarySchedule π) t y =
        rationalHittingValue (feedbackMatrix sys π) target t y := by
  intro t
  induction t with
  | zero =>
      intro y
      rfl
  | succ t ih =>
      intro y
      rw [policyValue_succ, rationalHittingValue_succ]
      by_cases hg : y ∈ target.goal
      · simp [hg]
      · simp only [if_neg hg]
        by_cases hd : y ∈ target.forbidden
        · simp [hd]
        · simp only [if_neg hd]
          change
            (∑ z : Fin n, (sys.matrix (π.choose y)).entry y z *
              policyValue sys target (stationarySchedule π) t z) =
            (∑ z : Fin n, (sys.matrix (π.choose y)).entry y z *
              rationalHittingValue (feedbackMatrix sys π) target t z)
          apply Finset.sum_congr rfl
          intro z _
          rw [ih z]

/-- Certified D1-A bridge: a STATIONARY schedule's algebraic evaluation
equals the actual canonical typed strategic-world hitting probability.
No such statement is yet claimed for arbitrary nonstationary schedules. -/
theorem stationarySchedule_value_eq_typed
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) (π : StateFeedback sys)
    (x : Fin n) (t : ℕ) :
    (policyValue sys target (stationarySchedule π) t x : ℝ) =
      hittingValue (typedTarget target)
        (feedbackModel sys π).inducedKernel
        (FiniteStrategicRealization.decode x) t := by
  rw [stationarySchedule_value_eq_rational sys target π t x]
  exact (ControlledKernel.feedback_typed_hitting_value sys π target x t).symm

end Bellman
end ReverseSolver
end PermanssonResearch
