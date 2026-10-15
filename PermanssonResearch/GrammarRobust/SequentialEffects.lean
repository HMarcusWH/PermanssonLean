import PermanssonLean.Regime.ConstitutiveMargin
import Mathlib.Tactic

/-!
# B2 — genuine four-corner strategic interventions

All four values evaluate the *same* original whole-path property map on
point-initialized canonical path laws.  The protocol admits each replacement
independently: arbitrary intervention families, including Lane B grammars,
are not presumed downward-closed or decomposable.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace GrammarRobust
namespace SequentialEffects

universe uS uX uA uC uZ

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable {Component : Type uC}

/-- A frozen, admitted experiment with exactly the same world transition at
all four corners.  Its three interventions are separately certified in F.
Field equalities concern *actual primitive kernels*, not component labels. -/
structure FourCornerProtocol
    (M : PermanssonLean.StrategicWorldModel S X A)
    (F : PermanssonLean.InterventionFamily M Component) where
  actionOnly : PermanssonLean.AdmissibleStrategicIntervention F
  updateOnly : PermanssonLean.AdmissibleStrategicIntervention F
  joint : PermanssonLean.AdmissibleStrategicIntervention F
  action_keeps_update :
    actionOnly.intervention.apply.generator.update = M.generator.update
  update_keeps_action :
    updateOnly.intervention.apply.generator.action = M.generator.action
  joint_matches_action :
    joint.intervention.apply.generator.action =
      actionOnly.intervention.apply.generator.action
  joint_matches_update :
    joint.intervention.apply.generator.update =
      updateOnly.intervention.apply.generator.update

variable {M : PermanssonLean.StrategicWorldModel S X A}
variable {F : PermanssonLean.InterventionFamily M Component}
variable {Z : Type uZ} [MetricSpace Z]

/-- The three held-P-fixed corners genuinely inherit the frozen world kernel. -/
theorem FourCornerProtocol.worlds_fixed (C : FourCornerProtocol M F) :
    C.actionOnly.intervention.apply.world = M.world ∧
    C.updateOnly.intervention.apply.world = M.world ∧
    C.joint.intervention.apply.world = M.world :=
  ⟨C.actionOnly.world_eq, C.updateOnly.world_eq, C.joint.world_eq⟩

noncomputable def baselineValue (C : FourCornerProtocol M F)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) : Z :=
  PermanssonLean.RegimeSpecification.baselinePropertyValue ψ M y

noncomputable def actionValue (C : FourCornerProtocol M F)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) : Z :=
  PermanssonLean.RegimeSpecification.intervenedPropertyValue
    ψ C.actionOnly.intervention y

noncomputable def updateValue (C : FourCornerProtocol M F)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) : Z :=
  PermanssonLean.RegimeSpecification.intervenedPropertyValue
    ψ C.updateOnly.intervention y

noncomputable def jointValue (C : FourCornerProtocol M F)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) : Z :=
  PermanssonLean.RegimeSpecification.intervenedPropertyValue
    ψ C.joint.intervention y

noncomputable def actionEffect (C : FourCornerProtocol M F)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) : ℝ :=
  dist (baselineValue C ψ y) (actionValue C ψ y)

noncomputable def updateEffect (C : FourCornerProtocol M F)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) : ℝ :=
  dist (baselineValue C ψ y) (updateValue C ψ y)

noncomputable def jointEffect (C : FourCornerProtocol M F)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) : ℝ :=
  dist (baselineValue C ψ y) (jointValue C ψ y)

/-- Diagnostic leg from action-only to joint, not original-baseline PR status. -/
noncomputable def condUpdateEffect (C : FourCornerProtocol M F)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) : ℝ :=
  dist (actionValue C ψ y) (jointValue C ψ y)

/-- Diagnostic leg from update-only to joint, not original-baseline PR status. -/
noncomputable def condActionEffect (C : FourCornerProtocol M F)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) : ℝ :=
  dist (updateValue C ψ y) (jointValue C ψ y)

theorem jointEffect_le_action_add_condUpdate
    (C : FourCornerProtocol M F)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) :
    jointEffect C ψ y ≤ actionEffect C ψ y + condUpdateEffect C ψ y := by
  dsimp [jointEffect, actionEffect, condUpdateEffect]
  exact dist_triangle _ _ _

theorem jointEffect_abs_action_sub_condUpdate_le
    (C : FourCornerProtocol M F)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) :
    |actionEffect C ψ y - condUpdateEffect C ψ y| ≤
      jointEffect C ψ y := by
  dsimp [actionEffect, condUpdateEffect, jointEffect]
  apply abs_le.mpr
  constructor
  · have h := dist_triangle (actionValue C ψ y) (baselineValue C ψ y)
      (jointValue C ψ y)
    rw [dist_comm (actionValue C ψ y) (baselineValue C ψ y)] at h
    linarith
  · have h := dist_triangle (baselineValue C ψ y) (jointValue C ψ y)
      (actionValue C ψ y)
    rw [dist_comm (jointValue C ψ y) (actionValue C ψ y)] at h
    linarith

theorem jointEffect_le_update_add_condAction
    (C : FourCornerProtocol M F)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) :
    jointEffect C ψ y ≤ updateEffect C ψ y + condActionEffect C ψ y := by
  dsimp [jointEffect, updateEffect, condActionEffect]
  exact dist_triangle _ _ _

theorem jointEffect_abs_update_sub_condAction_le
    (C : FourCornerProtocol M F)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) :
    |updateEffect C ψ y - condActionEffect C ψ y| ≤
      jointEffect C ψ y := by
  dsimp [updateEffect, condActionEffect, jointEffect]
  apply abs_le.mpr
  constructor
  · have h := dist_triangle (updateValue C ψ y) (baselineValue C ψ y)
      (jointValue C ψ y)
    rw [dist_comm (updateValue C ψ y) (baselineValue C ψ y)] at h
    linarith
  · have h := dist_triangle (baselineValue C ψ y) (jointValue C ψ y)
      (updateValue C ψ y)
    rw [dist_comm (jointValue C ψ y) (updateValue C ψ y)] at h
    linarith

/-- No direct subadditivity theorem in terms of the two baseline-relative
singleton legs is asserted: they are not a path between 00 and 11. -/

end SequentialEffects
end GrammarRobust
end PermanssonResearch
