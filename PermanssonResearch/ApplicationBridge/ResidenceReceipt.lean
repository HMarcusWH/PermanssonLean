import PermanssonResearch.ApplicationBridge.ControlTableReceipt
import PermanssonResearch.ReverseSolver.RollingResidenceTable
import PermanssonResearch.ReverseSolver.ResidenceSpecializationOptimality
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

/-! ## First-entry and danger-avoid residence

The generic array-backed `rollingMonitorTable` evaluates any monitor given an
explicit enumeration of its finite state type; `rollingMonitorTable_eq_value`
identifies every lookup with the Bellman value. Below are computable
enumerations of the first-entry and avoid monitor states, the resulting
executable values, and their transport to the existing behavioral-history
optimality theorems. -/

/-- `waiting ↦ 0`, `active k ↦ k + 1`, `failed ↦ m + 1`, `succeeded ↦ m + 2`. -/
def firstEntryEnumeration (m : ℕ) : Fin (m + 3) ≃ FirstState m where
  toFun i :=
    if h0 : i.val = 0 then .waiting
    else if ha : i.val ≤ m then .active ⟨i.val - 1, by omega⟩
    else if i.val = m + 1 then .failed
    else .succeeded
  invFun
    | .waiting => ⟨0, by omega⟩
    | .active k => ⟨k.val + 1, by have := k.isLt; omega⟩
    | .failed => ⟨m + 1, by omega⟩
    | .succeeded => ⟨m + 2, by omega⟩
  left_inv := by
    rintro ⟨i, hi⟩
    by_cases h0 : i = 0
    · subst h0
      rfl
    · by_cases ha : i ≤ m
      · simp only [h0, ha, dite_false, dite_true]
        ext
        simp only
        omega
      · by_cases hf : i = m + 1
        · subst hf
          simp
        · have h2 : i = m + 2 := by omega
          subst h2
          simp
  right_inv := by
    intro q
    cases q with
    | waiting => rfl
    | active k =>
        have hk := k.isLt
        have hle : k.val + 1 ≤ m := hk
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, dite_false, hle, dite_true,
          Nat.add_sub_cancel]
    | failed => simp
    | succeeded => simp

/-- Avoid states are a residence state and a danger flag. -/
def avoidEnumeration (m : ℕ) : Fin ((m + 2) * 2 * 2) ≃ AvoidState m :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (residenceEnumeration m) finTwoEquiv)

section Specializations

variable {C : Type*} [DecidableEq C] [Fintype C] {k : ℕ}

/-- Executable optimal first-entry residence value from `y`. -/
def rollingFirstEntryValue (sys : FiniteControlSystem C k) (G : Fin k → Prop)
    [DecidablePred G] (dwell latest : ℕ) (y : Fin k) : ℚ :=
  tableRead (firstEntryEnumeration dwell)
    (rollingMonitorTable sys (firstEntryMonitor G latest dwell).toMonitor
      (firstEntryEnumeration dwell) (latest + dwell) 0) y
    ((firstEntryMonitor G latest dwell).initial y)

theorem rollingFirstEntry_optimal_and_attained (sys : FiniteControlSystem C k)
    (G : Fin k → Prop) [DecidablePred G] (dwell latest : ℕ) (y : Fin k) :
    (∀ σ : BehavioralPolicy sys, behavioralFirstEntryProbability sys σ G dwell latest y ≤
      (rollingFirstEntryValue sys G dwell latest y : ℝ)) ∧
    (∃ σ : BehavioralPolicy sys, behavioralFirstEntryProbability sys σ G dwell latest y =
      (rollingFirstEntryValue sys G dwell latest y : ℝ)) := by
  simpa only [rollingFirstEntryValue, rollingMonitorTable_eq_value] using
    behavioralFirstEntry_optimal_and_attained sys G dwell latest y

/-- Executable optimal danger-avoid residence value from `y`. -/
def rollingAvoidValue (sys : FiniteControlSystem C k) (G D : Fin k → Prop)
    [DecidablePred G] [DecidablePred D] (dwell latest : ℕ) (y : Fin k) : ℚ :=
  tableRead (avoidEnumeration dwell)
    (rollingMonitorTable sys (avoidResidenceMonitor G D dwell).toMonitor
      (avoidEnumeration dwell) (latest + dwell) 0) y
    ((avoidResidenceMonitor G D dwell).initial y)

theorem rollingAvoid_optimal_and_attained (sys : FiniteControlSystem C k)
    (G D : Fin k → Prop) [DecidablePred G] [DecidablePred D] (dwell latest : ℕ) (y : Fin k) :
    (∀ σ : BehavioralPolicy sys, behavioralAvoidResidenceProbability sys σ G D dwell latest y ≤
      (rollingAvoidValue sys G D dwell latest y : ℝ)) ∧
    (∃ σ : BehavioralPolicy sys, behavioralAvoidResidenceProbability sys σ G D dwell latest y =
      (rollingAvoidValue sys G D dwell latest y : ℝ)) := by
  simpa only [rollingAvoidValue, rollingMonitorTable_eq_value] using
    behavioralAvoidResidence_optimal_and_attained sys G D dwell latest y

end Specializations

/-- Reported first-entry values are the executable optima at every start. -/
def checkFirstEntryValues (sys : FiniteControlSystem (Fin m) n) (target : Finset (Fin n))
    (dwell latest : ℕ) (values : Fin n → ℚ) : Bool :=
  decide (∀ y : Fin n, rollingFirstEntryValue sys (· ∈ target) dwell latest y = values y)

theorem checkFirstEntryValues_sound (sys : FiniteControlSystem (Fin m) n)
    (target : Finset (Fin n)) (dwell latest : ℕ) (values : Fin n → ℚ)
    (h : checkFirstEntryValues sys target dwell latest values = true) (y : Fin n) :
    (∀ σ : BehavioralPolicy sys,
      behavioralFirstEntryProbability sys σ (· ∈ target) dwell latest y ≤ (values y : ℝ)) ∧
    (∃ σ : BehavioralPolicy sys,
      behavioralFirstEntryProbability sys σ (· ∈ target) dwell latest y = (values y : ℝ)) := by
  unfold checkFirstEntryValues at h
  rw [← of_decide_eq_true h y]
  exact rollingFirstEntry_optimal_and_attained sys (· ∈ target) dwell latest y

/-- Reported danger-avoid values are the executable optima at every start. -/
def checkAvoidValues (sys : FiniteControlSystem (Fin m) n) (target danger : Finset (Fin n))
    (dwell latest : ℕ) (values : Fin n → ℚ) : Bool :=
  decide (∀ y : Fin n,
    rollingAvoidValue sys (· ∈ target) (· ∈ danger) dwell latest y = values y)

theorem checkAvoidValues_sound (sys : FiniteControlSystem (Fin m) n)
    (target danger : Finset (Fin n)) (dwell latest : ℕ) (values : Fin n → ℚ)
    (h : checkAvoidValues sys target danger dwell latest values = true) (y : Fin n) :
    (∀ σ : BehavioralPolicy sys,
      behavioralAvoidResidenceProbability sys σ (· ∈ target) (· ∈ danger) dwell latest y ≤
        (values y : ℝ)) ∧
    (∃ σ : BehavioralPolicy sys,
      behavioralAvoidResidenceProbability sys σ (· ∈ target) (· ∈ danger) dwell latest y =
        (values y : ℝ)) := by
  unfold checkAvoidValues at h
  rw [← of_decide_eq_true h y]
  exact rollingAvoid_optimal_and_attained sys (· ∈ target) (· ∈ danger) dwell latest y

end PermanssonResearch.ApplicationBridge.ResidenceReceipt
