import PermanssonResearch.ApplicationBridge.ControlTableReceipt
import PermanssonResearch.ReverseSolver.StationaryMenuOptimization
import PermanssonResearch.ReverseSolver.NonlinearBooleanClassEvaluator
import Mathlib.Tactic

/-!
# ApplicationBridge — nonlinear classwise occupation objectives

The supported functional is the frozen Boolean score `1 - |p - 2/3|` of the
true-descriptor share `p` of an occupation law. The objective of a
deterministic stationary feedback policy under an initial law `μ` is the
`μ`-mixture of `actualObjective`: the expectation of the functional of the
actual random occupation limit (C2), never the functional of its expectation.

A receipt lists the exact value of every admissible deterministic stationary
policy of a `FiniteControlSystem`, the optimum and the tie set. The check
enumerates every `StationaryChoice` of the system and evaluates the exact C10
absorption / C11 class-law arithmetic of `rationalObjective`; soundness
transfers each value to the actual objective (`rationalObjective_eq_actual`)
and the optimum to the whole declared policy class. With `boundControlSystem`
the policies are exactly the declared feasible action maps of a reflected
α/P/U model with P and U fixed. Randomized or history-dependent policies are
not compared.
-/

namespace PermanssonResearch.ApplicationBridge.NonlinearReceipt

open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.ControlledKernel
open PermanssonResearch.ReverseSolver.StationaryOccupation
open PermanssonResearch.ReverseSolver.NonlinearPeriodThree

set_option autoImplicit false

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {n : ℕ} [NeZero n]

/-- Exact initial-law objective of one deterministic stationary policy. -/
noncomputable def lawScore (h : Fin n → Bool) (sys : FiniteControlSystem C n) (μ : Fin n → ℚ)
    (f : StateFeedback sys) : ℚ :=
  ∑ y : Fin n, μ y * rationalObjective (booleanClassFunctional h) (feedbackMatrix sys f) y

/-- Expected Boolean score of the actual random occupation limit, mixed over
    the initial law. -/
noncomputable def actualLawScore (h : Fin n → Bool) (sys : FiniteControlSystem C n)
    (μ : Fin n → ℚ) (f : StateFeedback sys) : ℝ :=
  ∑ y : Fin n, (μ y : ℝ) * actualObjective (booleanClassFunctional h) (feedbackMatrix sys f) y

omit [Fintype C] in
theorem lawScore_eq_actual (h : Fin n → Bool) (sys : FiniteControlSystem C n)
    (μ : Fin n → ℚ) (f : StateFeedback sys) :
    (lawScore h sys μ f : ℝ) = actualLawScore h sys μ f := by
  unfold lawScore actualLawScore
  push_cast
  apply Finset.sum_congr rfl
  intro y _
  rw [boolean_rational_objective_eq_actual]

/-- Every admissible stationary policy has its listed value; the optimum
    bounds them all; the tie set is exactly the optimal policies. -/
def NonlinearChecks (h : Fin n → Bool) (sys : FiniteControlSystem C n) (μ : Fin n → ℚ)
    (values : (Fin n → C) → ℚ) (optimum : ℚ) (tied : Finset (Fin n → C)) : Prop :=
  (∀ π : StationaryChoice sys, lawScore h sys μ π.toFeedback = values π.val) ∧
  (∀ π : StationaryChoice sys, values π.val ≤ optimum) ∧
  (∀ π : StationaryChoice sys, π.val ∈ tied ↔ values π.val = optimum) ∧
  (∃ π : StationaryChoice sys, π.val ∈ tied)

noncomputable instance (h : Fin n → Bool) (sys : FiniteControlSystem C n) (μ : Fin n → ℚ)
    (values : (Fin n → C) → ℚ) (optimum : ℚ) (tied : Finset (Fin n → C)) :
    Decidable (NonlinearChecks h sys μ values optimum tied) := by
  unfold NonlinearChecks
  infer_instance

/-- Decided by kernel evaluation of the exact class arithmetic. -/
noncomputable def checkBooleanClassObjective (h : Fin n → Bool) (sys : FiniteControlSystem C n)
    (μ : Fin n → ℚ) (values : (Fin n → C) → ℚ) (optimum : ℚ)
    (tied : Finset (Fin n → C)) : Bool :=
  decide (NonlinearChecks h sys μ values optimum tied)

theorem checkBooleanClassObjective_sound (h : Fin n → Bool) (sys : FiniteControlSystem C n)
    (μ : Fin n → ℚ) (values : (Fin n → C) → ℚ) (optimum : ℚ)
    (tied : Finset (Fin n → C))
    (hc : checkBooleanClassObjective h sys μ values optimum tied = true) :
    NonlinearChecks h sys μ values optimum tied := by
  unfold checkBooleanClassObjective at hc
  exact of_decide_eq_true hc

section Receipt

variable (h : Fin n → Bool) (sys : FiniteControlSystem C n) (μ : Fin n → ℚ)
  (values : (Fin n → C) → ℚ) (optimum : ℚ) (tied : Finset (Fin n → C))
  (hc : checkBooleanClassObjective h sys μ values optimum tied = true)
include hc

/-- Every listed policy value is the actual expected classwise score. -/
theorem checked_classwise_objective (f : StateFeedback sys) :
    (values f.choose : ℝ) = actualLawScore h sys μ f := by
  have hv := (checkBooleanClassObjective_sound h sys μ values optimum tied hc).1
    (feedbackToChoice f)
  rw [← lawScore_eq_actual]
  exact_mod_cast hv.symm

/-- The checked optimum is attained and is the maximum of the actual
    objective over every admissible deterministic stationary policy; the tie
    set is exactly the set of optimal policies. -/
theorem checked_stationary_class_optimum :
    (∀ f : StateFeedback sys, actualLawScore h sys μ f ≤ optimum) ∧
    (∀ f : StateFeedback sys, f.choose ∈ tied ↔ actualLawScore h sys μ f = optimum) ∧
    ∃ f : StateFeedback sys, f.choose ∈ tied ∧ actualLawScore h sys μ f = optimum := by
  obtain ⟨-, hle, htied, ⟨π, hπ⟩⟩ := checkBooleanClassObjective_sound h sys μ values optimum tied hc
  have hval := checked_classwise_objective h sys μ values optimum tied hc
  refine ⟨fun f => ?_, fun f => ?_, ⟨π.toFeedback, hπ, ?_⟩⟩
  · rw [← hval]
    exact_mod_cast hle (feedbackToChoice f)
  · have ht := htied (feedbackToChoice f)
    change f.choose ∈ tied ↔ values f.choose = optimum at ht
    rw [← hval, ht]
    constructor <;> intro hx <;> exact_mod_cast hx
  · rw [← hval]
    exact_mod_cast (htied π).mp hπ

end Receipt

end PermanssonResearch.ApplicationBridge.NonlinearReceipt
