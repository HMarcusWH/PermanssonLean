import PermanssonResearch.ApplicationBridge.ControlTableReceipt
import PermanssonResearch.ReverseSolver.RollingResidenceTable
import Mathlib.Tactic

/-!
# ApplicationBridge — retryable residence value certificates

Reported per-start optimal probabilities of the literal retryable residence
event — a block of `dwell + 1` consecutive target observations starting by
observation time `latest` — are checked against the executable layer-wise
table `rollingResidenceValue` of the actual `FiniteControlSystem`. Soundness
transports the check to `rollingResidence_optimal_and_attained`: every real
full-history behavioral controller is bounded by the reported value and one
attains it.

With `boundControlSystem` the control system is the source's fixed-action
`P·U` rows with exactly its feasible actions. First-entry and danger-avoid
residence modes are not covered here. No empirical identification,
original-regime certification or release approval follows.
-/

namespace PermanssonResearch.ApplicationBridge.ResidenceReceipt

open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.ControlledKernel
open PermanssonResearch.ReverseSolver.FiniteMonitor

set_option autoImplicit false

variable {m n : ℕ}

/-- Every reported start value equals the exact optimal retryable residence
    value of the actual system for the target set. -/
def ResidenceChecks (sys : FiniteControlSystem (Fin m) n) (target : Finset (Fin n))
    (dwell latest : ℕ) (values : Fin n → ℚ) : Prop :=
  ∀ y : Fin n, rollingResidenceValue sys (· ∈ target) dwell latest y = values y

/-- The layer-wise table is executable rational arithmetic over finite data. -/
instance (sys : FiniteControlSystem (Fin m) n) (target : Finset (Fin n))
    (dwell latest : ℕ) (values : Fin n → ℚ) :
    Decidable (ResidenceChecks sys target dwell latest values) := by
  unfold ResidenceChecks
  infer_instance

/-- A false result means the reported values are wrong, not that the
    residence event is impossible. -/
def checkResidenceValues (sys : FiniteControlSystem (Fin m) n)
    (target : Finset (Fin n)) (dwell latest : ℕ) (values : Fin n → ℚ) : Bool :=
  decide (ResidenceChecks sys target dwell latest values)

theorem checkResidenceValues_complete (sys : FiniteControlSystem (Fin m) n)
    (target : Finset (Fin n)) (dwell latest : ℕ) (values : Fin n → ℚ)
    (h : checkResidenceValues sys target dwell latest values = true) :
    ResidenceChecks sys target dwell latest values := by
  unfold checkResidenceValues at h
  exact of_decide_eq_true h

/-- A checked value is the optimum of the literal retryable residence event
    over every real full-history behavioral controller, and is attained. -/
theorem checkResidenceValues_sound (sys : FiniteControlSystem (Fin m) n)
    (target : Finset (Fin n)) (dwell latest : ℕ) (values : Fin n → ℚ)
    (h : checkResidenceValues sys target dwell latest values = true) (y : Fin n) :
    (∀ σ : BehavioralPolicy sys,
      behavioralResidenceProbability sys σ (· ∈ target) dwell latest y ≤ (values y : ℝ)) ∧
    (∃ σ : BehavioralPolicy sys,
      behavioralResidenceProbability sys σ (· ∈ target) dwell latest y = (values y : ℝ)) := by
  rw [← checkResidenceValues_complete sys target dwell latest values h y]
  exact rollingResidence_optimal_and_attained sys (· ∈ target) dwell latest y

end PermanssonResearch.ApplicationBridge.ResidenceReceipt
