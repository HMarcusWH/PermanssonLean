import PermanssonLean.Intervention.Family
import PermanssonLean.StrategicWorld.InducedKernel

open ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- Apply exactly one target-indexed replacement to the baseline model.

The untouched primitives are copied from the baseline model by construction:
action-selection and update interventions leave P fixed; joint strategic
interventions replace the whole strategic generator while leaving P fixed;
world-transition interventions leave the strategic generator fixed.
-/
noncomputable def applyReplacement
    (M : StrategicWorldModel S X A) :
    (t : InterventionTarget) →
      InterventionReplacement S X A t →
      StrategicWorldModel S X A
  | .actionSelection, r =>
      { M with
        generator :=
          { M.generator with
            action := r.kernel
            action_isMarkov := r.isMarkov } }
  | .strategicUpdate, r =>
      { M with
        generator :=
          { M.generator with
            update := r.kernel
            update_isMarkov := r.isMarkov } }
  | .worldTransition, r =>
      { M with
        world := r.kernel
        world_isMarkov := r.isMarkov }
  | .jointStrategic, r =>
      { M with generator := r }

/-- The target-indexed replacement that simply reinstalls the baseline component. -/
noncomputable def baselineReplacement
    (M : StrategicWorldModel S X A) :
    (t : InterventionTarget) →
      InterventionReplacement S X A t
  | .actionSelection =>
      ⟨M.generator.action, M.generator.action_isMarkov⟩
  | .strategicUpdate =>
      ⟨M.generator.update, M.generator.update_isMarkov⟩
  | .worldTransition =>
      ⟨M.world, M.world_isMarkov⟩
  | .jointStrategic =>
      M.generator

@[simp]
theorem applyReplacement_baseline
    (M : StrategicWorldModel S X A)
    (t : InterventionTarget) :
    applyReplacement M t (baselineReplacement M t) = M := by
  cases M with
  | mk generator world world_isMarkov =>
      cases generator with
      | mk action update action_isMarkov update_isMarkov =>
          cases t <;> rfl

@[simp]
theorem applyReplacement_actionSelection_update
    (M : StrategicWorldModel S X A)
    (r : InterventionReplacement S X A .actionSelection) :
    (applyReplacement M .actionSelection r).generator.update =
      M.generator.update := rfl

@[simp]
theorem applyReplacement_actionSelection_world
    (M : StrategicWorldModel S X A)
    (r : InterventionReplacement S X A .actionSelection) :
    (applyReplacement M .actionSelection r).world = M.world := rfl

@[simp]
theorem applyReplacement_strategicUpdate_action
    (M : StrategicWorldModel S X A)
    (r : InterventionReplacement S X A .strategicUpdate) :
    (applyReplacement M .strategicUpdate r).generator.action =
      M.generator.action := rfl

@[simp]
theorem applyReplacement_strategicUpdate_world
    (M : StrategicWorldModel S X A)
    (r : InterventionReplacement S X A .strategicUpdate) :
    (applyReplacement M .strategicUpdate r).world = M.world := rfl

@[simp]
theorem applyReplacement_jointStrategic_world
    (M : StrategicWorldModel S X A)
    (r : InterventionReplacement S X A .jointStrategic) :
    (applyReplacement M .jointStrategic r).world = M.world := rfl

@[simp]
theorem applyReplacement_worldTransition_generator
    (M : StrategicWorldModel S X A)
    (r : InterventionReplacement S X A .worldTransition) :
    (applyReplacement M .worldTransition r).generator = M.generator := rfl

/-- Every strategic intervention holds the world-transition kernel P fixed. -/
theorem applyReplacement_world_eq_of_strategic
    (M : StrategicWorldModel S X A)
    {t : InterventionTarget}
    (r : InterventionReplacement S X A t)
    (ht : t.IsStrategic) :
    (applyReplacement M t r).world = M.world := by
  cases t <;>
    simp [InterventionTarget.IsStrategic, applyReplacement] at ht ⊢

namespace TypedIntervention

/-- Apply a frozen typed intervention to its baseline model. -/
noncomputable def apply
    {M : StrategicWorldModel S X A}
    {Component : Type uK}
    {F : InterventionFamily M Component}
    (J : TypedIntervention F) :
    StrategicWorldModel S X A :=
  applyReplacement M (F.targetOf J.component) J.replacement

/-- Canonical induced kernel of the intervened strategic-world model. -/
noncomputable def intervenedKernel
    {M : StrategicWorldModel S X A}
    {Component : Type uK}
    {F : InterventionFamily M Component}
    (J : TypedIntervention F) :
    Kernel (JointState S X) (JointState S X) :=
  J.apply.inducedKernel

/-- Every well-typed intervention still induces a Markov kernel. -/
theorem intervenedKernel_isMarkov
    {M : StrategicWorldModel S X A}
    {Component : Type uK}
    {F : InterventionFamily M Component}
    (J : TypedIntervention F) :
    IsMarkovKernel J.intervenedKernel := by
  exact StrategicWorldModel.inducedKernel_isMarkov J.apply

/-- Strategic typed interventions inherit the hold-P-fixed guarantee. -/
theorem world_eq_of_strategic
    {M : StrategicWorldModel S X A}
    {Component : Type uK}
    {F : InterventionFamily M Component}
    (J : TypedIntervention F)
    (hJ : J.IsStrategic) :
    J.apply.world = M.world := by
  exact applyReplacement_world_eq_of_strategic
    M J.replacement hJ

end TypedIntervention

/-- Bundled admissible strategic interventions necessarily hold P fixed. -/
theorem AdmissibleStrategicIntervention.world_eq
    {M : StrategicWorldModel S X A}
    {Component : Type uK}
    {F : InterventionFamily M Component}
    (J : AdmissibleStrategicIntervention F) :
    J.intervention.apply.world = M.world :=
  J.intervention.world_eq_of_strategic J.strategic

end PermanssonLean
