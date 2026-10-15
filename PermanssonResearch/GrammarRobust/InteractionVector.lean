import PermanssonResearch.GrammarRobust.ConditionalMargins
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-! B2 additive interaction is meaningful ONLY for normed additive outputs.
It is not the scalar expression joint distance minus singleton distances. -/

open MeasureTheory ProbabilityTheory Set
namespace PermanssonResearch.GrammarRobust.InteractionVector
open PermanssonLean
open SequentialEffects

universe uS uX uA uC uZ uH
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable {Component : Type uC}
variable {Z : Type uZ} [NormedAddCommGroup Z]
variable {H : Type uH} [MeasurableSpace H]
variable {M : StrategicWorldModel S X A}
variable {F : InterventionFamily M Component}
variable {spec : RegimeSpecification (JointState S X) H}

/-- A genuine original-path-law 2×2 additive difference. -/
noncomputable def interactionVector (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (y : JointState S X) : Z :=
  jointValue C ψ y - actionValue C ψ y -
    updateValue C ψ y + baselineValue C ψ y

theorem interactionVector_norm_le_condUpdate_add_update
    (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z) (y : JointState S X) :
    ‖interactionVector C ψ y‖ ≤
      condUpdateEffect C ψ y + updateEffect C ψ y := by
  have h : interactionVector C ψ y =
      (jointValue C ψ y - actionValue C ψ y) +
        (baselineValue C ψ y - updateValue C ψ y) := by
    unfold interactionVector
    abel
  rw [h]
  calc
    ‖(jointValue C ψ y - actionValue C ψ y) +
        (baselineValue C ψ y - updateValue C ψ y)‖ ≤
        ‖jointValue C ψ y - actionValue C ψ y‖ +
          ‖baselineValue C ψ y - updateValue C ψ y‖ :=
      norm_add_le _ _
    _ = condUpdateEffect C ψ y + updateEffect C ψ y := by
      simp only [condUpdateEffect, updateEffect, dist_eq_norm]
      rw [norm_sub_rev (jointValue C ψ y) (actionValue C ψ y)]

theorem interactionVector_norm_le_condAction_add_action
    (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z) (y : JointState S X) :
    ‖interactionVector C ψ y‖ ≤
      condActionEffect C ψ y + actionEffect C ψ y := by
  have h : interactionVector C ψ y =
      (jointValue C ψ y - updateValue C ψ y) +
        (baselineValue C ψ y - actionValue C ψ y) := by
    unfold interactionVector
    abel
  rw [h]
  calc
    ‖(jointValue C ψ y - updateValue C ψ y) +
        (baselineValue C ψ y - actionValue C ψ y)‖ ≤
        ‖jointValue C ψ y - updateValue C ψ y‖ +
          ‖baselineValue C ψ y - actionValue C ψ y‖ :=
      norm_add_le _ _
    _ = condActionEffect C ψ y + actionEffect C ψ y := by
      simp only [condActionEffect, actionEffect, dist_eq_norm]
      rw [norm_sub_rev (jointValue C ψ y) (updateValue C ψ y)]

/-- sSup is used with a separately proved bounded-above image. -/
noncomputable def uniformInteractionMagnitude
    (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec) :
    ℝ := sSup ((fun y => ‖interactionVector C ψ y‖) '' B₁.states)

theorem uniformInteractionMagnitude_le
    (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec)
    (R : ℝ)
    (hR : ∀ y ∈ B₁.states, ‖interactionVector C ψ y‖ ≤ R) :
    uniformInteractionMagnitude C ψ B₁ ≤ R := by
  unfold uniformInteractionMagnitude
  apply csSup_le
  · rcases B₁.states_nonempty M spec with ⟨y,hy⟩
    exact ⟨_, ⟨y,hy,rfl⟩⟩
  · rintro _ ⟨y,hy,rfl⟩
    exact hR y hy

end PermanssonResearch.GrammarRobust.InteractionVector
