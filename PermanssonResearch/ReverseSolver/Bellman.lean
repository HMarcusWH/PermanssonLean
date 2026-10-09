import PermanssonResearch.ReverseSolver.ControlledKernel
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# D1-B: finite-horizon exact-rational Bellman value

A fully observed finite control system has a nonempty finite admissible control
set at every state. The bestControl selector maximizes exact rational
one-step continuation scores. Goal/forbidden are terminal FOR EVALUATION ONLY.
This module makes no claim about a nonstationary typed trajectory measure.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace Bellman

open ControlledKernel
universe uC

/-- Exact one-step continuation score for a control. -/
def actionScore {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (v : Fin n → ℚ)
    (y : Fin n) (c : C) : ℚ :=
  ∑ z : Fin n, (sys.matrix c).entry y z * v z

/-- A finite nonempty admissible set attains a rational maximum. -/
noncomputable def bestControl {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (v : Fin n → ℚ)
    (y : Fin n) : C :=
  Classical.choose
    (Finset.exists_max_image (sys.options y) (actionScore sys v y)
      (sys.options_nonempty y))

theorem bestControl_mem {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (v : Fin n → ℚ)
    (y : Fin n) :
    bestControl sys v y ∈ sys.options y :=
  (Classical.choose_spec
    (Finset.exists_max_image (sys.options y) (actionScore sys v y)
      (sys.options_nonempty y))).1

theorem bestControl_dominates {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (v : Fin n → ℚ)
    (y : Fin n) (c : C) (hc : c ∈ sys.options y) :
    actionScore sys v y c ≤
      actionScore sys v y (bestControl sys v y) :=
  (Classical.choose_spec
    (Finset.exists_max_image (sys.options y) (actionScore sys v y)
      (sys.options_nonempty y))).2 c hc

/-- A maximum-action selector for every observed state. -/
noncomputable def bestFeedback {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (v : Fin n → ℚ) :
    StateFeedback sys where
  choose := bestControl sys v
  permitted := bestControl_mem sys v

/-- Exact Bellman recursion, indexed by transitions remaining. -/
noncomputable def bellmanValue {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (target : RationalHittingTarget n) :
    ℕ → Fin n → ℚ
  | 0, y => if y ∈ target.goal then 1 else 0
  | t + 1, y =>
      if y ∈ target.goal then 1
      else if y ∈ target.forbidden then 0
      else actionScore sys (bellmanValue sys target t) y
        (bestControl sys (bellmanValue sys target t) y)

@[simp] theorem bellmanValue_zero {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (target : RationalHittingTarget n)
    (y : Fin n) :
    bellmanValue sys target 0 y =
      if y ∈ target.goal then 1 else 0 := rfl

theorem bellmanValue_succ {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (target : RationalHittingTarget n)
    (t : ℕ) (y : Fin n) :
    bellmanValue sys target (t+1) y =
      if y ∈ target.goal then 1
      else if y ∈ target.forbidden then 0
      else actionScore sys (bellmanValue sys target t) y
        (bestControl sys (bellmanValue sys target t) y) := rfl

/-- A Bellman step attains the maximum of admissible continuation scores. -/
theorem bellmanValue_succ_maximizes {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (target : RationalHittingTarget n)
    (t : ℕ) (y : Fin n)
    (hg : y ∉ target.goal) (hd : y ∉ target.forbidden)
    (c : C) (hc : c ∈ sys.options y) :
    actionScore sys (bellmanValue sys target t) y c ≤
      bellmanValue sys target (t+1) y := by
  rw [bellmanValue_succ]
  simp only [if_neg hg, if_neg hd]
  exact bestControl_dominates sys (bellmanValue sys target t) y c hc

/-- Every stochastic row preserves bounds 0 and 1. -/
theorem actionScore_bounds {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (v : Fin n → ℚ)
    (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) (y : Fin n) (c : C) :
    0 ≤ actionScore sys v y c ∧ actionScore sys v y c ≤ 1 := by
  constructor
  · unfold actionScore
    exact Finset.sum_nonneg (fun z _ =>
      mul_nonneg ((sys.matrix c).entry_nonneg y z) (hv z).1)
  · unfold actionScore
    calc
      (∑ z : Fin n, (sys.matrix c).entry y z * v z) ≤
          ∑ z : Fin n, (sys.matrix c).entry y z * 1 := by
            apply Finset.sum_le_sum
            intro z hz
            exact mul_le_mul_of_nonneg_left (hv z).2
              ((sys.matrix c).entry_nonneg y z)
      _ = 1 := by simpa using (sys.matrix c).row_sum_one y

/-- Every Bellman value lies in the exact rational unit interval. -/
theorem bellmanValue_bounds {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (target : RationalHittingTarget n) :
    ∀ (t : ℕ) (y : Fin n),
      0 ≤ bellmanValue sys target t y ∧
        bellmanValue sys target t y ≤ 1 := by
  intro t
  induction t with
  | zero =>
      intro y
      simp only [bellmanValue_zero]
      split_ifs <;> norm_num
  | succ t ih =>
      intro y
      rw [bellmanValue_succ]
      by_cases hg : y ∈ target.goal
      · simp [hg]
      · simp only [if_neg hg]
        by_cases hd : y ∈ target.forbidden
        · simp [hd]
        · simpa only [if_neg hd] using
            actionScore_bounds sys (bellmanValue sys target t) ih y
              (bestControl sys (bellmanValue sys target t) y)

/-- An already-reached goal is always valued at one. -/
theorem bellmanValue_goal {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (target : RationalHittingTarget n)
    (t : ℕ) (y : Fin n) (hg : y ∈ target.goal) :
    bellmanValue sys target t y = 1 := by
  cases t with
  | zero => simp [bellmanValue_zero, hg]
  | succ t => simp [bellmanValue_succ, hg]

/-- A forbidden initial state is never counted as success. -/
theorem bellmanValue_forbidden {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (target : RationalHittingTarget n)
    (t : ℕ) (y : Fin n) (hd : y ∈ target.forbidden) :
    bellmanValue sys target t y = 0 := by
  have hg : y ∉ target.goal := by
    intro h
    exact (Finset.disjoint_left.mp target.disjoint) h hd
  cases t with
  | zero => simp [bellmanValue_zero, hg]
  | succ t => simp [bellmanValue_succ, hg, hd]

end Bellman
end ReverseSolver
end PermanssonResearch
