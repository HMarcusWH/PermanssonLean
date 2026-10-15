import PermanssonResearch.GrammarRobust.ConditionalMargins
import PermanssonResearch.GrammarRobust.BlockConstitution
import Mathlib.Tactic

/-!
# B2 — exact admitted-block-to-four-corner bridge

No downward-closure assumption: the three admitted blocks are independent
proof objects.  All four physical-atom selection conditions are required.
Consequently a coarse component containing both α and U cannot be silently
split into two admitted singleton components.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.GrammarRobust.SequentialBlockBridge
open PermanssonLean
open SequentialEffects
open ConditionalMargins

universe uS uX uA uI uJ uC uH uZ
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable {IA : Type uI} {IU : Type uJ} {C : Type uC}
variable [Fintype IA] [Fintype IU] [Fintype C]
variable [LinearOrder IA] [LinearOrder IU]

/-- Four actual admitted models, with a frozen identical world P.
Conditions concern physical atoms rather than merely semantic labels. -/
noncomputable def fromAllowed
    (M : StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU) (Γ : PartitionGrammar IA IU C)
    (Da Du Dj : AllowedBlock Γ)
    (hAA : actionAtoms (Γ.expand Da.components) =
      actionAtoms (Γ.expand Dj.components))
    (hAE : updateAtoms (Γ.expand Da.components) = ∅)
    (hUE : actionAtoms (Γ.expand Du.components) = ∅)
    (hUU : updateAtoms (Γ.expand Du.components) =
      updateAtoms (Γ.expand Dj.components)) :
    FourCornerProtocol M (blockFamily M bank Γ) where
  actionOnly := admittedBlockIntervention M bank Γ Da
  updateOnly := admittedBlockIntervention M bank Γ Du
  joint := admittedBlockIntervention M bank Γ Dj
  action_keeps_update := by
    change (patchedUpdate M bank (updateAtoms (Γ.expand Da.components))).kernel =
      M.generator.update
    rw [hAE]
    exact patchedUpdate_empty M bank
  update_keeps_action := by
    change (patchedAction M bank (actionAtoms (Γ.expand Du.components))).kernel =
      M.generator.action
    rw [hUE]
    exact patchedAction_empty M bank
  joint_matches_action := by
    change (patchedAction M bank (actionAtoms (Γ.expand Dj.components))).kernel =
      (patchedAction M bank (actionAtoms (Γ.expand Da.components))).kernel
    rw [hAA]
  joint_matches_update := by
    change (patchedUpdate M bank (updateAtoms (Γ.expand Dj.components))).kernel =
      (patchedUpdate M bank (updateAtoms (Γ.expand Du.components))).kernel
    rw [hUU]

variable {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace H] [MetricSpace Z]
variable {M : StrategicWorldModel S X A}
variable {bank : AtomicBank M IA IU}
variable {Γ : PartitionGrammar IA IU C}
variable {Da Du Dj : AllowedBlock Γ}
variable {hAA : actionAtoms (Γ.expand Da.components) =
  actionAtoms (Γ.expand Dj.components)}
variable {hAE : updateAtoms (Γ.expand Da.components) = ∅}
variable {hUE : actionAtoms (Γ.expand Du.components) = ∅}
variable {hUU : updateAtoms (Γ.expand Du.components) =
  updateAtoms (Γ.expand Dj.components)}

theorem actionEffect_eq_original
    (ψ : RegimePropertyMap (JointState S X) Z) (y : JointState S X) :
    actionEffect (fromAllowed M bank Γ Da Du Dj hAA hAE hUE hUU) ψ y =
      blockEffect M bank Γ Da ψ y := rfl

theorem updateEffect_eq_original
    (ψ : RegimePropertyMap (JointState S X) Z) (y : JointState S X) :
    updateEffect (fromAllowed M bank Γ Da Du Dj hAA hAE hUE hUU) ψ y =
      blockEffect M bank Γ Du ψ y := rfl

theorem jointEffect_eq_original
    (ψ : RegimePropertyMap (JointState S X) Z) (y : JointState S X) :
    jointEffect (fromAllowed M bank Γ Da Du Dj hAA hAE hUE hUU) ψ y =
      blockEffect M bank Γ Dj ψ y := rfl

theorem jointMargin_eq_original
    (spec : RegimeSpecification (JointState S X) H)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : RegimeSpecification.ConstitutiveComparisonSet M spec) :
    jointMargin (fromAllowed M bank Γ Da Du Dj hAA hAE hUE hUU) ψ B₁ =
      blockMargin M bank Γ Dj spec ψ B₁ := rfl

theorem actionMargin_eq_original
    (spec : RegimeSpecification (JointState S X) H)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : RegimeSpecification.ConstitutiveComparisonSet M spec) :
    actionMargin (fromAllowed M bank Γ Da Du Dj hAA hAE hUE hUU) ψ B₁ =
      blockMargin M bank Γ Da spec ψ B₁ := rfl

theorem updateMargin_eq_original
    (spec : RegimeSpecification (JointState S X) H)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : RegimeSpecification.ConstitutiveComparisonSet M spec) :
    updateMargin (fromAllowed M bank Γ Da Du Dj hAA hAE hUE hUU) ψ B₁ =
      blockMargin M bank Γ Du spec ψ B₁ := rfl

end PermanssonResearch.GrammarRobust.SequentialBlockBridge
