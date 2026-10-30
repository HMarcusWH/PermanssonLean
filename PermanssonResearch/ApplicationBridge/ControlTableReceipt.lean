import PermanssonResearch.ReverseSolver.BellmanOptimality
import Mathlib.Tactic

/-!
# ApplicationBridge — bounded exact Bellman table certificates

A complete finite rational value/choice table is checked against the actual
FiniteControlSystem, its admitted controls, and the original hitting target.
The checker is finite (Fin N), not a search for a presumed optimum.
Soundness transports the checked values to the existing Bellman theorem.

A FiniteControlSystem must itself be bound to source-model P/U kernels before
this proves anything about an externally submitted alpha/P/U application.
No empirical identification, original-regime certification, or release
approval follows from this module alone.
-/

namespace PermanssonResearch.ApplicationBridge.ControlTableReceipt

open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.ControlledKernel
open PermanssonResearch.ReverseSolver.Bellman

set_option autoImplicit false

variable {m n : ℕ}

/-- Full finite receipt obligations. The reported table uses t transitions
    remaining; chosen t is applied with t+1 remaining.
    Terminal states need not have winning actions, but selected controls are
    always admitted. All ties are permitted when their scores are maximal. -/
def TableChecks (sys : FiniteControlSystem (Fin m) n)
    (target : RationalHittingTarget n) (N : ℕ)
    (values : ℕ → Fin n → ℚ) (chosen : ℕ → Fin n → Fin m) : Prop :=
  (∀ y : Fin n, values 0 y = if y ∈ target.goal then 1 else 0) ∧
  (∀ t : Fin N, ∀ y : Fin n,
    values (t.val + 1) y =
      if y ∈ target.goal then 1
      else if y ∈ target.forbidden then 0
      else actionScore sys (values t.val) y (chosen t.val y)) ∧
  (∀ t : Fin N, ∀ y : Fin n, chosen t.val y ∈ sys.options y) ∧
  (∀ t : Fin N, ∀ y : Fin n,
    y ∉ target.goal → y ∉ target.forbidden →
      ∀ c : Fin m, c ∈ sys.options y →
        actionScore sys (values t.val) y c ≤
          actionScore sys (values t.val) y (chosen t.val y))

/-- Executable on finite rational data. A false result is not evidence of
    infeasibility: it means the supplied table fails these obligations. -/
def checkBellmanReceipt (sys : FiniteControlSystem (Fin m) n)
    (target : RationalHittingTarget n) (N : ℕ)
    (values : ℕ → Fin n → ℚ) (chosen : ℕ → Fin n → Fin m) : Bool :=
  decide (TableChecks sys target N values chosen)

/-- A successful Boolean check produces the entire proof obligation,
    not a caller-owned assertion that the receipt was accepted. -/
theorem checkBellmanReceipt_complete
    (sys : FiniteControlSystem (Fin m) n)
    (target : RationalHittingTarget n) (N : ℕ)
    (values : ℕ → Fin n → ℚ) (chosen : ℕ → Fin n → Fin m)
    (h : checkBellmanReceipt sys target N values chosen = true) :
    TableChecks sys target N values chosen := by
  exact of_decide_eq_true h

/-- Exact recurrence plus complete action comparison yields the original
    Bellman value for every state and every declared horizon. -/
theorem checked_table_eq_bellman
    (sys : FiniteControlSystem (Fin m) n)
    (target : RationalHittingTarget n) (N : ℕ)
    (values : ℕ → Fin n → ℚ) (chosen : ℕ → Fin n → Fin m)
    (h : TableChecks sys target N values chosen) :
    ∀ t : ℕ, t ≤ N → ∀ y : Fin n,
      values t y = bellmanValue sys target t y := by
  rcases h with ⟨hzero, hstep, hpermitted, hmax⟩
  intro t
  induction t with
  | zero =>
      intro _ y
      simpa only [bellmanValue_zero] using hzero y
  | succ t ih =>
      intro hle y
      have ht : t < N := Nat.lt_of_succ_le hle
      rw [hstep (⟨t, ht⟩ : Fin N) y, bellmanValue_succ]
      by_cases hg : y ∈ target.goal
      · simp [hg]
      · simp only [if_neg hg]
        by_cases hd : y ∈ target.forbidden
        · simp [hd]
        · simp only [if_neg hd]
          have hprev : values t = bellmanValue sys target t := by
            funext z
            exact ih (Nat.le_of_lt ht) z
          rw [hprev]
          apply le_antisymm
          · exact bestControl_dominates sys (bellmanValue sys target t) y
              (chosen t y) (hpermitted (⟨t, ht⟩ : Fin N) y)
          · have hbest := hmax (⟨t, ht⟩ : Fin N) y hg hd
                (bestControl sys (bellmanValue sys target t) y)
                (bestControl_mem sys (bellmanValue sys target t) y)
            simpa only [hprev] using hbest

/-- Successful checking identifies the Bellman value and thus bounds every
    admitted remaining-horizon Markov schedule; one schedule attains it.
    No identity with an arbitrary tied solver-selected vector is assumed. -/
theorem checkBellmanReceipt_sound
    (sys : FiniteControlSystem (Fin m) n)
    (target : RationalHittingTarget n) (N : ℕ)
    (values : ℕ → Fin n → ℚ) (chosen : ℕ → Fin n → Fin m)
    (h : checkBellmanReceipt sys target N values chosen = true) :
    (∀ y : Fin n, values N y = bellmanValue sys target N y) ∧
    (∀ (π : MarkovSchedule sys) (y : Fin n),
      policyValue sys target π N y ≤ values N y) ∧
    (∃ π : MarkovSchedule sys, ∀ y : Fin n,
      policyValue sys target π N y = values N y) := by
  have heq := checked_table_eq_bellman sys target N values chosen
    (checkBellmanReceipt_complete sys target N values chosen h)
  refine ⟨fun y => heq N (Nat.le_refl N) y, ?_, ?_⟩
  · intro π y
    rw [heq N (Nat.le_refl N) y]
    exact policyValue_le_bellman sys target π N y
  · refine ⟨maximizingSchedule sys target, ?_⟩
    intro y
    rw [heq N (Nat.le_refl N) y]
    exact maximizingSchedule_attains sys target N y

/-- The selected receipt action is admitted and locally maximal at every
    nonterminal state, even in the presence of tied maxima. -/
theorem checkBellmanReceipt_selected
    (sys : FiniteControlSystem (Fin m) n)
    (target : RationalHittingTarget n) (N : ℕ)
    (values : ℕ → Fin n → ℚ) (chosen : ℕ → Fin n → Fin m)
    (h : checkBellmanReceipt sys target N values chosen = true)
    (t : Fin N) (y : Fin n)
    (hg : y ∉ target.goal) (hd : y ∉ target.forbidden) :
    chosen t.val y ∈ sys.options y ∧
    ∀ c : Fin m, c ∈ sys.options y →
      actionScore sys (values t.val) y c ≤
        actionScore sys (values t.val) y (chosen t.val y) := by
  rcases checkBellmanReceipt_complete sys target N values chosen h with
    ⟨_, _, hp, hm⟩
  exact ⟨hp t y, hm t y hg hd⟩

end PermanssonResearch.ApplicationBridge.ControlTableReceipt
