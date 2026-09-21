import PermanssonLean.Regime.RepresentationEquivalence
import PermanssonLean.Regime.ConstitutiveMargin

open MeasureTheory ProbabilityTheory Set

namespace PermanssonLean

universe uS uX uA uH uZ uK₁ uK₂

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
variable [TopologicalSpace S] [TopologicalSpace X]

namespace RegimeSpecification

theorem intervenedPropertyValue_eq_of_inducedKernel_eq
    {M₁ M₂ : StrategicWorldModel S X A}
    {Component₁ : Type uK₁} {Component₂ : Type uK₂}
    {F₁ : InterventionFamily M₁ Component₁}
    {F₂ : InterventionFamily M₂ Component₂}
    (ψ : RegimePropertyMap (JointState S X) Z)
    (J₁ : AdmissibleStrategicIntervention F₁)
    (J₂ : AdmissibleStrategicIntervention F₂)
    (hJ :
      J₁.intervention.apply.inducedKernel =
        J₂.intervention.apply.inducedKernel)
    (y : JointState S X) :
    intervenedPropertyValue ψ J₁.intervention y =
      intervenedPropertyValue ψ J₂.intervention y := by
  unfold intervenedPropertyValue
  rw [pathProbability_eq_of_inducedKernel_eq
    J₁.intervention.apply J₂.intervention.apply hJ]

/-- Proposition 7.4, pointwise form: matched baseline and post-intervention
kernels preserve the constitutive classification on the same frozen B₁ state
set, transported across the representation change. -/
theorem strategicallyConstitutive_iff_of_kernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    {Component₁ : Type uK₁} {Component₂ : Type uK₂}
    (F₁ : InterventionFamily M₁ Component₁)
    (F₂ : InterventionFamily M₂ Component₂)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M₁ spec)
    (J₁ : AdmissibleStrategicIntervention F₁)
    (J₂ : AdmissibleStrategicIntervention F₂)
    (hJ :
      J₁.intervention.apply.inducedKernel =
        J₂.intervention.apply.inducedKernel) :
    IsStrategicallyConstitutive M₁ spec F₁ ψ B₁ J₁ ↔
      IsStrategicallyConstitutive M₂ spec F₂ ψ
        (B₁.transport M₁ M₂ hK spec) J₂ := by
  constructor
  · intro h y hy
    have hy' : y ∈ B₁.states := by simpa using hy
    have hbase :=
      baselinePropertyValue_eq_of_inducedKernel_eq M₁ M₂ hK ψ y
    have hinter :=
      intervenedPropertyValue_eq_of_inducedKernel_eq ψ J₁ J₂ hJ y
    simpa [hbase, hinter] using h y hy'
  · intro h y hy
    have hy' : y ∈ (B₁.transport M₁ M₂ hK spec).states := by
      simpa using hy
    have hbase :=
      baselinePropertyValue_eq_of_inducedKernel_eq M₁ M₂ hK ψ y
    have hinter :=
      intervenedPropertyValue_eq_of_inducedKernel_eq ψ J₁ J₂ hJ y
    simpa [hbase, hinter] using h y hy'

section Metric

variable [MetricSpace Z]

/-- Matched interventions preserve the exact pointwise constitutive effect. -/
theorem constitutiveEffect_eq_of_kernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    {Component₁ : Type uK₁} {Component₂ : Type uK₂}
    {F₁ : InterventionFamily M₁ Component₁}
    {F₂ : InterventionFamily M₂ Component₂}
    (ψ : RegimePropertyMap (JointState S X) Z)
    (J₁ : AdmissibleStrategicIntervention F₁)
    (J₂ : AdmissibleStrategicIntervention F₂)
    (hJ :
      J₁.intervention.apply.inducedKernel =
        J₂.intervention.apply.inducedKernel)
    (y : JointState S X) :
    constitutiveEffect M₁ ψ J₁ y =
      constitutiveEffect M₂ ψ J₂ y := by
  unfold constitutiveEffect
  rw [
    baselinePropertyValue_eq_of_inducedKernel_eq M₁ M₂ hK ψ y,
    intervenedPropertyValue_eq_of_inducedKernel_eq ψ J₁ J₂ hJ y
  ]

/-- Matched interventions preserve the exact uniform constitutive margin. -/
theorem constitutiveMargin_eq_of_kernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    {Component₁ : Type uK₁} {Component₂ : Type uK₂}
    (F₁ : InterventionFamily M₁ Component₁)
    (F₂ : InterventionFamily M₂ Component₂)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M₁ spec)
    (J₁ : AdmissibleStrategicIntervention F₁)
    (J₂ : AdmissibleStrategicIntervention F₂)
    (hJ :
      J₁.intervention.apply.inducedKernel =
        J₂.intervention.apply.inducedKernel) :
    constitutiveMargin M₁ spec F₁ ψ B₁ J₁ =
      constitutiveMargin M₂ spec F₂ ψ
        (B₁.transport M₁ M₂ hK spec) J₂ := by
  unfold constitutiveMargin
  apply congrArg sInf
  change
    constitutiveEffect M₁ ψ J₁ '' B₁.states =
      constitutiveEffect M₂ ψ J₂ '' B₁.states
  apply Set.image_congr
  intro y hy
  exact constitutiveEffect_eq_of_kernel_eq M₁ M₂ hK ψ J₁ J₂ hJ y

theorem uniformlyConstitutive_iff_of_kernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    {Component₁ : Type uK₁} {Component₂ : Type uK₂}
    (F₁ : InterventionFamily M₁ Component₁)
    (F₂ : InterventionFamily M₂ Component₂)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M₁ spec)
    (J₁ : AdmissibleStrategicIntervention F₁)
    (J₂ : AdmissibleStrategicIntervention F₂)
    (hJ :
      J₁.intervention.apply.inducedKernel =
        J₂.intervention.apply.inducedKernel) :
    IsUniformlyStrategicallyConstitutive M₁ spec F₁ ψ B₁ J₁ ↔
      IsUniformlyStrategicallyConstitutive M₂ spec F₂ ψ
        (B₁.transport M₁ M₂ hK spec) J₂ := by
  rw [
    uniformlyConstitutive_iff_margin_pos,
    uniformlyConstitutive_iff_margin_pos,
    constitutiveMargin_eq_of_kernel_eq
      M₁ M₂ hK spec F₁ F₂ ψ B₁ J₁ J₂ hJ
  ]

end Metric

end RegimeSpecification

end PermanssonLean
