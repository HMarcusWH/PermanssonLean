import PermanssonResearch.GrammarRobust.BooleanMinimalityCases
import Mathlib.Tactic

/-!
# Lane B B4 — genuinely different atom banks with exactly the same baseline

Two frozen physical banks share the *same baseline* model and world P.
The first sets α=false and U=false jointly; the alternate bank leaves
α=true and sets U=false. They give different pointwise induced kernels.
Thus baseline equivalence does NOT identify block-intervention effects.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust
namespace AlternativeBankWitness

open PermanssonLean PermanssonLean.RegimeSpecification BooleanModel BooleanBaseline BooleanDynamics
open BooleanMinimalityCases

/-- A distinct post-intervention bank over the very same baseline model.
The action replacement is the baseline α; its update replacement is U=false. -/
noncomputable def alternative :
    AtomicBank baseline (Fin 1) (Fin 1) where
  action := fun _ => {
    region := Set.univ
    measurable_region := MeasurableSet.univ
    replacement := actionTrue
    replacement_isMarkov := by unfold actionTrue; infer_instance }
  update := fun _ => {
    region := Set.univ
    measurable_region := MeasurableSet.univ
    replacement := updateFalse
    replacement_isMarkov := by unfold updateFalse; infer_instance }
  action_disjoint := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))
  update_disjoint := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))

private theorem action_as_baseline :
    (patchedAction baseline alternative ({0} : Finset (Fin 1))).kernel =
      actionTrue := by
  apply Kernel.ext
  intro y
  have hy : y ∈ (alternative.action (0 : Fin 1)).region := by
    simp [alternative]
  have h := applyRowPatch_selected (alternative.action (0 : Fin 1))
    (⟨baseline.generator.action, baseline.generator.action_isMarkov⟩ :
      MarkovKernelReplacement Y Bool) y hy
  have hrow :
      (patchedAction baseline alternative ({0} : Finset (Fin 1))).kernel y =
        (alternative.action (0 : Fin 1)).replacement y := by
    simpa [patchedAction] using h
  simpa [alternative] using hrow

private theorem update_as_false :
    (patchedUpdate baseline alternative ({0} : Finset (Fin 1))).kernel =
      updateFalse := by
  apply Kernel.ext
  intro y
  have hy : y ∈ (alternative.update (0 : Fin 1)).region := by
    simp [alternative]
  have h := applyRowPatch_selected (alternative.update (0 : Fin 1))
    (⟨baseline.generator.update, baseline.generator.update_isMarkov⟩ :
      MarkovKernelReplacement (UpdateInput Bool Bool Bool) Bool) y hy
  have hrow :
      (patchedUpdate baseline alternative ({0} : Finset (Fin 1))).kernel y =
        (alternative.update (0 : Fin 1)).replacement y := by
    simpa [patchedUpdate] using h
  simpa [alternative] using hrow

/-- This is a real α/P/U induced-kernel calculation, not a Boolean
oracle: the action remains true and the strategic update becomes false. -/
theorem alternate_joint_inducedKernel (y : Y) :
    (blockModel baseline alternative fine joint).inducedKernel y =
      Measure.dirac updateDest := by
  classical
  have hα : (blockModel baseline alternative fine joint).generator.action =
      actionTrue := by
    change (patchedAction baseline alternative
      (actionAtoms (fine.expand joint))).kernel = actionTrue
    have he : actionAtoms (fine.expand joint) =
        ({0} : Finset (Fin 1)) := by
      ext i
      fin_cases i
      simp [actionAtoms, PartitionGrammar.expand, fine, joint]
    rw [he]
    exact action_as_baseline
  have hU : (blockModel baseline alternative fine joint).generator.update =
      updateFalse := by
    change (patchedUpdate baseline alternative
      (updateAtoms (fine.expand joint))).kernel = updateFalse
    have he : updateAtoms (fine.expand joint) =
        ({0} : Finset (Fin 1)) := by
      ext i
      fin_cases i
      simp [updateAtoms, PartitionGrammar.expand, fine, joint]
    rw [he]
    exact update_as_false
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply
    (blockModel baseline alternative fine joint) y hE]
  rw [hα, hU, blockModel_world]
  simp [actionTrue, updateFalse, baseline, worldCopy,
    Kernel.deterministic_apply, Measure.dirac_apply, updateDest]
  by_cases hmem : (false, true) ∈ E <;> simp [hmem]

/-- B4: the baseline is definitionally shared, P is definitionally held
fixed, but the two corresponding JOINT interventions differ in actual
induced probability law at every initial joint state. -/
theorem same_baseline_different_joint_laws (y : Y) :
    (blockModel baseline alternative fine joint).inducedKernel y ≠
      (blockModel baseline bank fine joint).inducedKernel y := by
  rw [alternate_joint_inducedKernel, joint_inducedKernel]
  intro h
  have he := congrArg (fun μ : Measure Y =>
    μ ({updateDest} : Set Y)) h
  have hne : updateDest ≠ jointDest := by decide
  simpa [Measure.dirac_apply', hne] using he


/-- B4 strengthened: the same baseline and original comparison set produce
*different original canonical path-law constitutive effects* for the same
joint component block under the two frozen physical banks. The OR event is
not constitutively changed by the alternative bank because its destination
retains one true coordinate. -/
theorem alternative_OR_value (y : Y) :
    PermanssonLean.RegimeSpecification.intervenedPropertyValue
      (BooleanOneStepEvents.propertyAtOne BooleanOneStepEvents.orP)
      (admittedBlockIntervention baseline alternative fine
        BooleanPersistence.jointBlock).intervention y = 1 := by
  change BooleanOneStepEvents.propertyAtOne BooleanOneStepEvents.orP
    (pathProbability
      (admittedBlockIntervention baseline alternative fine
        BooleanPersistence.jointBlock).intervention.apply
      (diracProba y)) = 1
  rw [admittedBlockIntervention_apply]
  change BooleanOneStepEvents.propertyAtOne BooleanOneStepEvents.orP
    (pathProbability (blockModel baseline alternative fine joint)
      (diracProba y)) = 1
  have h := BooleanOneStepEvents.propertyAtOne_eq_of_constantKernel
    (blockModel baseline alternative fine joint) updateDest
    alternate_joint_inducedKernel BooleanOneStepEvents.orP y
  simpa [BooleanOneStepEvents.orP, updateDest] using h

theorem alternative_OR_effect_zero (y : Y) :
    blockEffect baseline alternative fine BooleanPersistence.jointBlock
      (BooleanOneStepEvents.propertyAtOne BooleanOneStepEvents.orP) y = 0 := by
  unfold blockEffect PermanssonLean.RegimeSpecification.constitutiveEffect
  have hb := BooleanOneStepEvents.baseline_value BooleanOneStepEvents.orP y
  have ha := alternative_OR_value y
  rw [hb, ha]
  simp [BooleanOneStepEvents.orP, BooleanBaseline.q0]

theorem alternative_OR_margin_zero :
    blockMargin baseline alternative fine BooleanPersistence.jointBlock spec
      (BooleanOneStepEvents.propertyAtOne BooleanOneStepEvents.orP)
      comparison = 0 := by
  apply blockMargin_eq_of_constant_effect
  intro y _
  exact alternative_OR_effect_zero y

theorem B4_distinct_frozen_constitutive_margins :
    blockMargin baseline bank fine BooleanPersistence.jointBlock spec
      (BooleanOneStepEvents.propertyAtOne BooleanOneStepEvents.orP)
      comparison = 1 ∧
    blockMargin baseline alternative fine BooleanPersistence.jointBlock spec
      (BooleanOneStepEvents.propertyAtOne BooleanOneStepEvents.orP)
      comparison = 0 := by
  exact ⟨BooleanEffects.or_joint_margin_one, alternative_OR_margin_zero⟩


end AlternativeBankWitness
end GrammarRobust
end PermanssonResearch
