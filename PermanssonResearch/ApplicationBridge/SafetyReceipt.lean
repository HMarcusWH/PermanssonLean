import PermanssonResearch.ApplicationBridge.ControlTableReceipt
import PermanssonResearch.ReverseSolver.InfiniteSafetyOptimality
import Mathlib.Tactic

/-!
# ApplicationBridge — finite almost-sure safety core certificates

A reported safe core `S ⊆ G` and stationary witness controls are checked
against the actual `FiniteControlSystem`: `S` must be the finite pruning fixed
point `invariantCore sys G`, and every witness control must be admitted and
keep the next state inside `S` with probability one. Soundness transports the
check to the existing infinite-horizon theorems: membership in `S` is exactly
almost-sure safety of the actual path law under some full-history behavioral
controller, and outside `S` every controller fails with positive probability.

The excluded states' survival probability need not be zero. No empirical
identification, original-regime certification or release approval follows.
-/

namespace PermanssonResearch.ApplicationBridge.SafetyReceipt

open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.ControlledKernel
open PermanssonResearch.ReverseSolver.FiniteMonitor
open PermanssonResearch.ReverseSolver.InfiniteSafety

set_option autoImplicit false

variable {m n : ℕ}

/-- Full finite core obligations: pruning fixed point and witness closure. -/
def CoreChecks (sys : FiniteControlSystem (Fin m) n) (G S : Finset (Fin n))
    (witness : Fin n → Fin m) : Prop :=
  invariantCore sys G = S ∧
  ∀ y ∈ S, witness y ∈ sys.options y ∧ stays sys (witness y) y S

/-- Finset equality, bounded membership, admitted options and the positive
    support of exact rational rows are all decidable. -/
instance (sys : FiniteControlSystem (Fin m) n) (G S : Finset (Fin n))
    (witness : Fin n → Fin m) : Decidable (CoreChecks sys G S witness) := by
  unfold CoreChecks
  infer_instance

/-- Executable on finite rational data. A false result is not evidence that
    a state is unsafe: it means the supplied core or witness is wrong. -/
def checkInvariantCore (sys : FiniteControlSystem (Fin m) n)
    (G S : Finset (Fin n)) (witness : Fin n → Fin m) : Bool :=
  decide (CoreChecks sys G S witness)

theorem checkInvariantCore_complete (sys : FiniteControlSystem (Fin m) n)
    (G S : Finset (Fin n)) (witness : Fin n → Fin m)
    (h : checkInvariantCore sys G S witness = true) :
    CoreChecks sys G S witness := by
  unfold checkInvariantCore at h
  exact of_decide_eq_true h

/-- The reported core is the greatest controlled-invariant subset of `G`. -/
theorem checked_invariant_core_eq (sys : FiniteControlSystem (Fin m) n)
    (G S : Finset (Fin n)) (witness : Fin n → Fin m)
    (h : checkInvariantCore sys G S witness = true) :
    invariantCore sys G = S ∧ S ⊆ G ∧ controlledInvariant sys S ∧
      ∀ T : Finset (Fin n), T ⊆ G → controlledInvariant sys T → T ⊆ S := by
  have hcore := (checkInvariantCore_complete sys G S witness h).1
  subst hcore
  exact ⟨rfl, invariantCore_subset sys G, invariantCore_invariant sys G,
    fun T hTG hT => invariantCore_greatest sys G T hTG hT⟩

/-- Every reported witness control is admitted and closes the core. -/
theorem checked_witness_closed (sys : FiniteControlSystem (Fin m) n)
    (G S : Finset (Fin n)) (witness : Fin n → Fin m)
    (h : checkInvariantCore sys G S witness = true) (y : Fin n) (hy : y ∈ S) :
    witness y ∈ sys.options y ∧ rowMass sys (witness y) y S = 1 := by
  obtain ⟨hopt, hstay⟩ := (checkInvariantCore_complete sys G S witness h).2 y hy
  exact ⟨hopt, (stays_iff_rowMass_one sys (witness y) y S).mp hstay⟩

/-- Infinite-horizon characterization on the actual path law: a state is in
    the checked core iff some full-history behavioral controller keeps the
    trajectory in `G` forever with probability one. -/
theorem checked_core_iff_almostSureSafety (sys : FiniteControlSystem (Fin m) n)
    (G S : Finset (Fin n)) (witness : Fin n → Fin m)
    (h : checkInvariantCore sys G S witness = true) (y : Fin n) :
    y ∈ S ↔ ∃ σ : BehavioralPolicy sys, safetyProbability sys σ G y = 1 := by
  rw [← (checkInvariantCore_complete sys G S witness h).1]
  exact invariantCore_iff_almostSureSafety sys G y

/-- Outside the checked core no admitted behavioral controller is almost
    surely safe; survival may still be positive. -/
theorem checked_outside_core_not_almost_sure (sys : FiniteControlSystem (Fin m) n)
    (G S : Finset (Fin n)) (witness : Fin n → Fin m)
    (h : checkInvariantCore sys G S witness = true) (y : Fin n) (hy : y ∉ S)
    (σ : BehavioralPolicy sys) : safetyProbability sys σ G y < 1 := by
  have hle : safetyProbability sys σ G y ≤ 1 :=
    (infiniteSafety_upper sys σ G y).trans (limitValue_bounds sys G y).2
  refine lt_of_le_of_ne hle (fun heq => hy ?_)
  exact (checked_core_iff_almostSureSafety sys G S witness h y).mpr ⟨σ, heq⟩

/-- One deterministic stationary controller attains the infinite safety
    value at every state simultaneously, against every behavioral past. -/
theorem checked_infinite_safety_optimum (sys : FiniteControlSystem (Fin m) n)
    (G S : Finset (Fin n)) (witness : Fin n → Fin m)
    (h : checkInvariantCore sys G S witness = true) :
    (∀ y, y ∈ S ↔ limitValue sys G y = 1) ∧
    ∃ π : StateFeedback sys, ∀ y : Fin n,
      safetyProbability sys (stationaryBehavioral sys π) G y = limitValue sys G y ∧
      ∀ σ : BehavioralPolicy sys, safetyProbability sys σ G y ≤ limitValue sys G y := by
  refine ⟨fun y => ?_, deterministic_stationary_infinite_optimum sys G⟩
  rw [checked_core_iff_almostSureSafety sys G S witness h y]
  constructor
  · rintro ⟨σ, hσ⟩
    exact le_antisymm (limitValue_bounds sys G y).2
      (by simpa only [hσ] using infiniteSafety_upper sys σ G y)
  · intro hv
    exact ⟨stationaryBehavioral sys (stationaryPolicy sys G),
      (infiniteSafety_stationary_attains sys G y).trans hv⟩

end PermanssonResearch.ApplicationBridge.SafetyReceipt
