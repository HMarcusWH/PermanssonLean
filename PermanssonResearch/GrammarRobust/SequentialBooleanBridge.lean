import PermanssonResearch.GrammarRobust.SequentialBlockBridge
import PermanssonResearch.GrammarRobust.BooleanEffects
import PermanssonResearch.GrammarRobust.BooleanPersistence
import Mathlib.Tactic

/-! B2 witness transport: the original genuine Boolean α→P→U path-law
proofs provide exact zero singleton and one joint/conditional margins.
No new PR existence theorem is claimed. -/

namespace PermanssonResearch.GrammarRobust.SequentialBooleanBridge
open PermanssonLean PermanssonLean.RegimeSpecification
open SequentialEffects ConditionalMargins
open SequentialBlockBridge
open BooleanModel BooleanBaseline BooleanDynamics BooleanPersistence
open BooleanOneStepEvents BooleanEffects

private theorem fine_AA :
    actionAtoms (fine.expand actionBlock.components) =
      actionAtoms (fine.expand jointBlock.components) := by
  classical
  ext i
  fin_cases i
  simp [actionAtoms, PartitionGrammar.expand, fine, actionBlock, jointBlock,
    actionOnly, joint]

private theorem fine_AE :
    updateAtoms (fine.expand actionBlock.components) = ∅ := by
  classical
  ext i
  fin_cases i
  simp [updateAtoms, PartitionGrammar.expand, fine, actionBlock, actionOnly]

private theorem fine_UE :
    actionAtoms (fine.expand updateBlock.components) = ∅ := by
  classical
  ext i
  fin_cases i
  simp [actionAtoms, PartitionGrammar.expand, fine, updateBlock, updateOnly]

private theorem fine_UU :
    updateAtoms (fine.expand updateBlock.components) =
      updateAtoms (fine.expand jointBlock.components) := by
  classical
  ext i
  fin_cases i
  simp [updateAtoms, PartitionGrammar.expand, fine, updateBlock, jointBlock,
    updateOnly, joint]

/-- Exactly the existing three admitted fine-grammar Boolean blocks. -/
noncomputable def booleanCorners :
    FourCornerProtocol baseline (blockFamily baseline bank fine) :=
  fromAllowed baseline bank fine actionBlock updateBlock jointBlock
    fine_AA fine_AE fine_UE fine_UU

theorem boolean_jointMargin_survival_one :
    jointMargin booleanCorners persistenceProperty comparison = 1 := by
  change blockMargin baseline bank fine jointBlock spec
    persistenceProperty comparison = 1
  exact jointMargin_eq_one

theorem boolean_jointMargin_OR_one :
    jointMargin booleanCorners (propertyAtOne orP) comparison = 1 := by
  change blockMargin baseline bank fine jointBlock spec
    (propertyAtOne orP) comparison = 1
  exact or_joint_margin_one

theorem boolean_survival_action_null :
    ∀ y ∈ comparison.states, actionEffect booleanCorners persistenceProperty y = 0 := by
  intro y hy
  change blockEffect baseline bank fine actionBlock persistenceProperty y = 0
  exact actionEffect_eq_zero hy

theorem boolean_survival_update_null :
    ∀ y ∈ comparison.states, updateEffect booleanCorners persistenceProperty y = 0 := by
  intro y hy
  change blockEffect baseline bank fine updateBlock persistenceProperty y = 0
  exact updateEffect_eq_zero hy

theorem boolean_OR_action_null :
    ∀ y ∈ comparison.states,
      actionEffect booleanCorners (propertyAtOne orP) y = 0 := by
  intro y hy
  change blockEffect baseline bank fine actionBlock (propertyAtOne orP) y = 0
  exact or_action_zero y

theorem boolean_OR_update_null :
    ∀ y ∈ comparison.states,
      updateEffect booleanCorners (propertyAtOne orP) y = 0 := by
  intro y hy
  change blockEffect baseline bank fine updateBlock (propertyAtOne orP) y = 0
  exact or_update_zero y

theorem boolean_jointOnly_conditionalMargin_one :
    condUpdateMargin booleanCorners persistenceProperty comparison = 1 ∧
    condActionMargin booleanCorners persistenceProperty comparison = 1 := by
  obtain ⟨h1,h2⟩ :=
    jointOnly_conditionalMargins_eq_jointMargin booleanCorners
      persistenceProperty comparison boolean_survival_action_null
      boolean_survival_update_null
  exact ⟨h1.trans boolean_jointMargin_survival_one,
    h2.trans boolean_jointMargin_survival_one⟩

theorem boolean_OR_jointOnly_conditionalMargin_one :
    condUpdateMargin booleanCorners (propertyAtOne orP) comparison = 1 ∧
    condActionMargin booleanCorners (propertyAtOne orP) comparison = 1 := by
  obtain ⟨h1,h2⟩ :=
    jointOnly_conditionalMargins_eq_jointMargin booleanCorners
      (propertyAtOne orP) comparison boolean_OR_action_null boolean_OR_update_null
  exact ⟨h1.trans boolean_jointMargin_OR_one, h2.trans boolean_jointMargin_OR_one⟩

/-- Formal rejection of the false direct baseline-singleton subadditivity. -/
theorem boolean_naiveSubadditivity_false :
    ¬ (∀ y ∈ comparison.states,
      jointEffect booleanCorners persistenceProperty y ≤
        actionEffect booleanCorners persistenceProperty y +
          updateEffect booleanCorners persistenceProperty y) := by
  intro h
  obtain ⟨y,hy⟩ := comparison.states_nonempty baseline spec
  have hj : jointEffect booleanCorners persistenceProperty y = 1 := by
    change blockEffect baseline bank fine jointBlock persistenceProperty y = 1
    exact jointEffect_eq_one hy
  have ha := boolean_survival_action_null y hy
  have hu := boolean_survival_update_null y hy
  have hh := h y hy
  linarith

/-- The witness is also a genuine generalized original PR, not a table. -/
theorem boolean_joint_is_uniform_original_PR :
    IsUniformGeneralizedPermanssonRegimeRelative
      baseline spec referenceMeasure
      (blockFamily baseline bank fine) persistenceProperty comparison
      (admittedBlockIntervention baseline bank fine jointBlock) :=
  uniformRelativePR

end PermanssonResearch.GrammarRobust.SequentialBooleanBridge
