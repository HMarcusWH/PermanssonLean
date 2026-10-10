import PermanssonResearch.GrammarRobust.BooleanOccupation
import PermanssonResearch.GrammarRobust.SingleTargetBridge
import Mathlib.Tactic

/-!
# Lane B — real jointly intervened Boolean transition laws

These are equalities for `StrategicWorldModel.inducedKernel` computed from
actual action/world/update Markov kernels after the frozen atom selection.
The truth values are not axioms or manually asserted effects.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust
namespace BooleanDynamics

open PermanssonLean BooleanModel BooleanBaseline

def actionOnly : Finset (Fin 2) := {0}
def updateOnly : Finset (Fin 2) := {1}
def joint : Finset (Fin 2) := {0, 1}

def actionDest : Y := (true, false)
def updateDest : Y := (false, true)
def jointDest : Y := (false, false)

theorem actionOnly_inducedKernel (y : Y) :
    (blockModel baseline bank fine actionOnly).inducedKernel y =
      Measure.dirac actionDest := by
  classical
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply]
  simp [blockModel, atomicBlockModel, PartitionGrammar.expand,
    fine, actionOnly, actionAtoms, updateAtoms,
    patchedAction, patchedUpdate, applyRowPatch, bank, baseline,
    actionTrue, actionFalse, updateTrue, updateFalse, worldCopy,
    Kernel.piecewise_apply, Kernel.deterministic_apply,
    Measure.dirac_apply, actionDest]
  by_cases hmem : (true, false) ∈ E <;> simp [hmem]

theorem updateOnly_inducedKernel (y : Y) :
    (blockModel baseline bank fine updateOnly).inducedKernel y =
      Measure.dirac updateDest := by
  classical
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply]
  simp [blockModel, atomicBlockModel, PartitionGrammar.expand,
    fine, updateOnly, actionAtoms, updateAtoms,
    patchedAction, patchedUpdate, applyRowPatch, bank, baseline,
    actionTrue, actionFalse, updateTrue, updateFalse, worldCopy,
    Kernel.piecewise_apply, Kernel.deterministic_apply,
    Measure.dirac_apply, updateDest]
  by_cases hmem : (false, true) ∈ E <;> simp [hmem]

theorem joint_inducedKernel (y : Y) :
    (blockModel baseline bank fine joint).inducedKernel y =
      Measure.dirac jointDest := by
  classical
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply]
  simp [blockModel, atomicBlockModel, PartitionGrammar.expand,
    fine, joint, actionAtoms, updateAtoms,
    patchedAction, patchedUpdate, applyRowPatch, bank, baseline,
    actionTrue, actionFalse, updateTrue, updateFalse, worldCopy,
    Kernel.piecewise_apply, Kernel.deterministic_apply,
    Measure.dirac_apply, jointDest]
  by_cases hmem : (false, false) ∈ E <;> simp [hmem]

end BooleanDynamics
end GrammarRobust
end PermanssonResearch
