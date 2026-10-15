import PermanssonResearch.GrammarRobust.SequentialEffects
import Mathlib.Tactic

/-! B2 uniform conditional margins.  B₁ remains the original certified
comparison set, and a conditional leg is NOT original-baseline constitution. -/

open MeasureTheory ProbabilityTheory Set
namespace PermanssonResearch.GrammarRobust.ConditionalMargins
open PermanssonLean PermanssonLean.RegimeSpecification
open SequentialEffects

universe uS uX uA uC uZ uH
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable {Component : Type uC} {Z : Type uZ} [MetricSpace Z]
variable {H : Type uH} [MeasurableSpace H]
variable {M : StrategicWorldModel S X A}
variable {F : InterventionFamily M Component}
variable {spec : RegimeSpecification (JointState S X) H}

noncomputable def marginOf (B : Set (JointState S X))
    (f : JointState S X → ℝ) : ℝ := sInf (f '' B)

theorem marginOf_le (B : Set (JointState S X))
    (f : JointState S X → ℝ)
    (hf : ∀ y ∈ B, 0 ≤ f y)
    {y : JointState S X} (hy : y ∈ B) :
    marginOf B f ≤ f y := by
  unfold marginOf
  refine csInf_le ?_ ⟨y, hy, rfl⟩
  exact ⟨0, by rintro _ ⟨z,hz,rfl⟩; exact hf z hz⟩

theorem marginOf_congr (B : Set (JointState S X))
    (f g : JointState S X → ℝ) (h : ∀ y ∈ B, f y = g y) :
    marginOf B f = marginOf B g := by
  unfold marginOf
  congr 1
  exact Set.image_congr h

noncomputable def actionMargin (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) : ℝ :=
  marginOf B₁.states (actionEffect C ψ)
noncomputable def updateMargin (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) : ℝ :=
  marginOf B₁.states (updateEffect C ψ)
noncomputable def jointMargin (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) : ℝ :=
  marginOf B₁.states (jointEffect C ψ)
noncomputable def condUpdateMargin (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) : ℝ :=
  marginOf B₁.states (condUpdateEffect C ψ)
noncomputable def condActionMargin (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) : ℝ :=
  marginOf B₁.states (condActionEffect C ψ)

theorem jointMargin_eq_constitutiveMargin
    (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) :
    jointMargin C ψ B₁ = constitutiveMargin M spec F ψ B₁ C.joint := rfl
theorem actionMargin_eq_constitutiveMargin
    (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) :
    actionMargin C ψ B₁ = constitutiveMargin M spec F ψ B₁ C.actionOnly := rfl
theorem updateMargin_eq_constitutiveMargin
    (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) :
    updateMargin C ψ B₁ = constitutiveMargin M spec F ψ B₁ C.updateOnly := rfl

theorem jointMargin_le_effect (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    {y : JointState S X} (hy : y ∈ B₁.states) :
    jointMargin C ψ B₁ ≤ jointEffect C ψ y := by
  exact marginOf_le B₁.states (jointEffect C ψ)
    (by intro _ _; exact dist_nonneg) hy

theorem condUpdateMargin_ge_joint_sub_action (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) (ε : ℝ)
    (hε : ∀ y ∈ B₁.states, actionEffect C ψ y ≤ ε) :
    jointMargin C ψ B₁ - ε ≤ condUpdateMargin C ψ B₁ := by
  unfold condUpdateMargin marginOf
  apply le_csInf
  · rcases B₁.states_nonempty M spec with ⟨y,hy⟩
    exact ⟨condUpdateEffect C ψ y, ⟨y,hy,rfl⟩⟩
  · rintro _ ⟨y,hy,rfl⟩
    have hj := jointMargin_le_effect C ψ B₁ hy
    have ht := jointEffect_le_action_add_condUpdate C ψ y
    have he := hε y hy
    linarith

theorem condActionMargin_ge_joint_sub_update (C : FourCornerProtocol M F)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) (ε : ℝ)
    (hε : ∀ y ∈ B₁.states, updateEffect C ψ y ≤ ε) :
    jointMargin C ψ B₁ - ε ≤ condActionMargin C ψ B₁ := by
  unfold condActionMargin marginOf
  apply le_csInf
  · rcases B₁.states_nonempty M spec with ⟨y,hy⟩
    exact ⟨condActionEffect C ψ y, ⟨y,hy,rfl⟩⟩
  · rintro _ ⟨y,hy,rfl⟩
    have hj := jointMargin_le_effect C ψ B₁ hy
    have ht := jointEffect_le_update_add_condAction C ψ y
    have he := hε y hy
    linarith

end PermanssonResearch.GrammarRobust.ConditionalMargins
