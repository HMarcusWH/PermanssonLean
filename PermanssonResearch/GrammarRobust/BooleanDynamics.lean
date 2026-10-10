import PermanssonResearch.GrammarRobust.BooleanOccupation
import PermanssonResearch.GrammarRobust.SingleTargetBridge
import Mathlib.Tactic

/-!
# Lane B — canonical Dirac laws of all Boolean physical intervention blocks

Unlike a direct unfolding of the whole alpha/P/U nesting, these proofs first
evaluate the frozen component->atom map, then establish whole replacement
kernel equalities using the selected-row lemma, and *only then* compute the
resulting induced kernel. This prevents opaque markov-kernel proof fields from
being mistaken for an alternative intervention semantics.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust
namespace BooleanDynamics

open PermanssonLean BooleanModel BooleanBaseline

noncomputable section

def actionOnly : Finset (Fin 2) := {0}
def updateOnly : Finset (Fin 2) := {1}
def joint : Finset (Fin 2) := {0, 1}

def actionDest : Y := (true, false)
def updateDest : Y := (false, true)
def jointDest : Y := (false, false)

private theorem actionAtoms_actionOnly :
    actionAtoms (fine.expand actionOnly) =
      ({0} : Finset (Fin 1)) := by
  classical
  ext i
  fin_cases i
  simp [actionAtoms, PartitionGrammar.expand, fine, actionOnly]

private theorem updateAtoms_actionOnly :
    updateAtoms (fine.expand actionOnly) =
      (∅ : Finset (Fin 1)) := by
  classical
  ext i
  fin_cases i
  simp [updateAtoms, PartitionGrammar.expand, fine, actionOnly]

private theorem actionAtoms_updateOnly :
    actionAtoms (fine.expand updateOnly) =
      (∅ : Finset (Fin 1)) := by
  classical
  ext i
  fin_cases i
  simp [actionAtoms, PartitionGrammar.expand, fine, updateOnly]

private theorem updateAtoms_updateOnly :
    updateAtoms (fine.expand updateOnly) =
      ({0} : Finset (Fin 1)) := by
  classical
  ext i
  fin_cases i
  simp [updateAtoms, PartitionGrammar.expand, fine, updateOnly]

private theorem actionAtoms_joint :
    actionAtoms (fine.expand joint) =
      ({0} : Finset (Fin 1)) := by
  classical
  ext i
  fin_cases i
  simp [actionAtoms, PartitionGrammar.expand, fine, joint]

private theorem updateAtoms_joint :
    updateAtoms (fine.expand joint) =
      ({0} : Finset (Fin 1)) := by
  classical
  ext i
  fin_cases i
  simp [updateAtoms, PartitionGrammar.expand, fine, joint]

private theorem action_patch_is_false :
    (patchedAction baseline bank ({0} : Finset (Fin 1))).kernel =
      actionFalse := by
  apply Kernel.ext
  intro y
  have hy : y ∈ (bank.action (0 : Fin 1)).region := by
    simp [bank]
  have hrow := applyRowPatch_selected (bank.action (0 : Fin 1))
    (⟨baseline.generator.action, baseline.generator.action_isMarkov⟩ :
      MarkovKernelReplacement Y Bool) y hy
  have hselected :
      (patchedAction baseline bank ({0} : Finset (Fin 1))).kernel y =
        (bank.action (0 : Fin 1)).replacement y := by
    simpa [patchedAction] using hrow
  simpa [bank] using hselected

private theorem update_patch_is_false :
    (patchedUpdate baseline bank ({0} : Finset (Fin 1))).kernel =
      updateFalse := by
  apply Kernel.ext
  intro y
  have hy : y ∈ (bank.update (0 : Fin 1)).region := by
    simp [bank]
  have hrow := applyRowPatch_selected (bank.update (0 : Fin 1))
    (⟨baseline.generator.update, baseline.generator.update_isMarkov⟩ :
      MarkovKernelReplacement (UpdateInput Bool Bool Bool) Bool) y hy
  have hselected :
      (patchedUpdate baseline bank ({0} : Finset (Fin 1))).kernel y =
        (bank.update (0 : Fin 1)).replacement y := by
    simpa [patchedUpdate] using hrow
  simpa [bank] using hselected

private theorem actionOnly_action :
    (blockModel baseline bank fine actionOnly).generator.action =
      actionFalse := by
  change (patchedAction baseline bank (actionAtoms (fine.expand actionOnly))).kernel =
    actionFalse
  rw [actionAtoms_actionOnly]
  exact action_patch_is_false

private theorem actionOnly_update :
    (blockModel baseline bank fine actionOnly).generator.update =
      updateTrue := by
  change (patchedUpdate baseline bank (updateAtoms (fine.expand actionOnly))).kernel =
    updateTrue
  rw [updateAtoms_actionOnly]
  exact (patchedUpdate_empty baseline bank)

private theorem updateOnly_action :
    (blockModel baseline bank fine updateOnly).generator.action =
      actionTrue := by
  change (patchedAction baseline bank (actionAtoms (fine.expand updateOnly))).kernel =
    actionTrue
  rw [actionAtoms_updateOnly]
  exact (patchedAction_empty baseline bank)

private theorem updateOnly_update :
    (blockModel baseline bank fine updateOnly).generator.update =
      updateFalse := by
  change (patchedUpdate baseline bank (updateAtoms (fine.expand updateOnly))).kernel =
    updateFalse
  rw [updateAtoms_updateOnly]
  exact update_patch_is_false

private theorem joint_action :
    (blockModel baseline bank fine joint).generator.action =
      actionFalse := by
  change (patchedAction baseline bank (actionAtoms (fine.expand joint))).kernel =
    actionFalse
  rw [actionAtoms_joint]
  exact action_patch_is_false

private theorem joint_update :
    (blockModel baseline bank fine joint).generator.update =
      updateFalse := by
  change (patchedUpdate baseline bank (updateAtoms (fine.expand joint))).kernel =
    updateFalse
  rw [updateAtoms_joint]
  exact update_patch_is_false

theorem actionOnly_inducedKernel (y : Y) :
    (blockModel baseline bank fine actionOnly).inducedKernel y =
      Measure.dirac actionDest := by
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply
    (blockModel baseline bank fine actionOnly) y hE]
  rw [actionOnly_action, actionOnly_update]
  simp [actionFalse, updateTrue, blockModel_world, baseline, worldCopy,
    Kernel.deterministic_apply, Measure.dirac_apply, actionDest]
  by_cases hmem : (true, false) ∈ E <;> simp [hmem]

theorem updateOnly_inducedKernel (y : Y) :
    (blockModel baseline bank fine updateOnly).inducedKernel y =
      Measure.dirac updateDest := by
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply
    (blockModel baseline bank fine updateOnly) y hE]
  rw [updateOnly_action, updateOnly_update]
  simp [actionTrue, updateFalse, blockModel_world, baseline, worldCopy,
    Kernel.deterministic_apply, Measure.dirac_apply, updateDest]
  by_cases hmem : (false, true) ∈ E <;> simp [hmem]

theorem joint_inducedKernel (y : Y) :
    (blockModel baseline bank fine joint).inducedKernel y =
      Measure.dirac jointDest := by
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply
    (blockModel baseline bank fine joint) y hE]
  rw [joint_action, joint_update]
  simp [actionFalse, updateFalse, blockModel_world, baseline, worldCopy,
    Kernel.deterministic_apply, Measure.dirac_apply, jointDest]
  by_cases hmem : (false, false) ∈ E <;> simp [hmem]

end
end BooleanDynamics
end GrammarRobust
end PermanssonResearch
