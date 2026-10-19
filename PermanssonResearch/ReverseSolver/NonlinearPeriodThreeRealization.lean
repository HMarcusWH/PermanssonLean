import PermanssonLean.StrategicWorld.InducedKernel
import Mathlib.Tactic

/-!
# NEXT-06.1 — Native phase/world strategic model

A phase-aware deterministic controller and every deterministic phase-blind
physical feedback controller inhabit the SAME typed S = Fin 3, X = Bool,
A = Bool model. The physical transition copies the realized action and
the strategic update advances phase modulo three. Only alpha changes.

This first-stage module constructs the actual alpha -> P -> U kernel and
proves the exact atoms of that kernel, including all 36 ordered state pairs.
It does not assert an infinite-path occupation limit, universal policy
optimality, or a typed quotient to Unit × Fin 6.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.ReverseSolver.NonlinearPeriodThree

set_option autoImplicit false
open PermanssonLean

abbrev Phase := Fin 3
abbrev State := JointState Phase Bool

def nextPhase (p : Phase) : Phase := p + 1

/-- The same physical P for every compared controller: x' = realized action. -/
noncomputable def physicalWorld :
    Kernel (WorldInput Phase Bool Bool) Bool :=
  Kernel.deterministic (fun v => v.2) Measurable.of_discrete

/-- The same strategic U: only phase memory advances; it does not read the policy. -/
noncomputable def phaseUpdate :
    Kernel (UpdateInput Phase Bool Bool) Phase :=
  Kernel.deterministic (fun v => nextPhase v.1.1.1) Measurable.of_discrete

noncomputable def actionKernel (policy : State → Bool) : Kernel State Bool :=
  Kernel.deterministic policy Measurable.of_discrete

noncomputable def typedModel (policy : State → Bool) :
    StrategicWorldModel Phase Bool Bool where
  generator := {
    action := actionKernel policy
    update := phaseUpdate
    action_isMarkov := by
      unfold actionKernel
      infer_instance
    update_isMarkov := by
      unfold phaseUpdate
      infer_instance
  }
  world := physicalWorld
  world_isMarkov := by
    unfold physicalWorld
    infer_instance

def phaseAwarePolicy (y : State) : Bool := y.1 != (2 : Phase)

def phaseBlindPolicy (policy : Bool → Bool) (y : State) : Bool :=
  policy y.2

/-- This is the genuine one-step state update of the typed model. -/
def nextState (policy : State → Bool) (y : State) : State :=
  (nextPhase y.1, policy y)

noncomputable def periodThreeModel : StrategicWorldModel Phase Bool Bool :=
  typedModel phaseAwarePolicy

noncomputable def phaseBlindModel (policy : Bool → Bool) :
    StrategicWorldModel Phase Bool Bool :=
  typedModel (phaseBlindPolicy policy)

theorem period_three_world_fixed (p q : State → Bool) :
    (typedModel p).world = (typedModel q).world := rfl

theorem period_three_update_fixed (p q : State → Bool) :
    (typedModel p).generator.update = (typedModel q).generator.update := by
  change phaseUpdate = phaseUpdate
  rfl

/-- A singleton atom of the genuine typed induced kernel, not a proposed table. -/
theorem induced_kernel_singleton (policy : State → Bool) (y z : State) :
    (typedModel policy).inducedKernel y {z} =
      if nextState policy y = z then 1 else 0 := by
  rw [StrategicWorldModel.inducedKernel_apply
    (typedModel policy) y (measurableSet_singleton z)]
  simp [typedModel, actionKernel, physicalWorld, phaseUpdate,
    nextState, Kernel.deterministic_apply, Measure.dirac_apply']
  by_cases h : (nextPhase y.1, policy y) = z
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

/-- The explicit rational row is a theorem target, not an assumed kernel. -/
def rationalAtom (policy : State → Bool) (y z : State) : ℚ :=
  if nextState policy y = z then 1 else 0

/-- For every ordered pair of the six native states (all 36 entries). -/
theorem period_three_matrix_eq_induced
    (policy : State → Bool) (y z : State) :
    (typedModel policy).inducedKernel y {z} =
      ENNReal.ofReal (rationalAtom policy y z : ℝ) := by
  rw [induced_kernel_singleton]
  by_cases h : nextState policy y = z
  · simp [rationalAtom, h]
  · simp [rationalAtom, h]

theorem native_row_total (policy : State → Bool) (y : State) :
    (∑ z : State, rationalAtom policy y z) = (1 : ℚ) := by
  classical
  simp [rationalAtom]

def start : State := (0, false)

/-- The exact native cycle, including its strategic-memory coordinates. -/
theorem phase_aware_cycle :
    nextState phaseAwarePolicy start = (1, true) ∧
    nextState phaseAwarePolicy (1, true) = (2, true) ∧
    nextState phaseAwarePolicy (2, true) = start := by
  decide

/-- The phase-aware policy cannot be represented by Bool-only feedback. -/
theorem phase_aware_not_phase_blind (policy : Bool → Bool) :
    phaseAwarePolicy ≠ phaseBlindPolicy policy := by
  intro h
  have h0 := congrArg (fun f : State → Bool => f (0, false)) h
  have h2 := congrArg (fun f : State → Bool => f (2, false)) h
  simp [phaseAwarePolicy, phaseBlindPolicy] at h0 h2
  rw [h0] at h2
  cases h2

end PermanssonResearch.ReverseSolver.NonlinearPeriodThree
