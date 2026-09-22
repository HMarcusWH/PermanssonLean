import PermanssonLean.Regime.GroundedPermansson
import PermanssonLean.Regime.UniformPermansson

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH uG uZ uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {G : Type uG} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MeasurableSpace G]
variable [TopologicalSpace S] [TopologicalSpace X]
variable [MetricSpace Z]

namespace RegimeSpecification

/-- Uniform grounded confirmatory PR_g relative to one frozen protocol. -/
def IsGroundedConfirmatoryUniformPermanssonRegimeRelative
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) : Prop :=
  IsConfirmatoryGeneratedRegime M spec m ∧
  IsUniformlyStrategicallyConstitutive M spec F ψ B₁ J ∧
  IsGroundedPropertyRelative M spec F ψ g J

theorem groundedUniformPR_margin_pos
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsGroundedConfirmatoryUniformPermanssonRegimeRelative
      M spec m F ψ g B₁ J) :
    0 < constitutiveMargin M spec F ψ B₁ J :=
  (uniformlyConstitutive_iff_margin_pos M spec F ψ B₁ J).1 h.2.1

theorem groundedUniformPR_implies_groundedPR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsGroundedConfirmatoryUniformPermanssonRegimeRelative
      M spec m F ψ g B₁ J) :
    IsGroundedConfirmatoryPermanssonRegimeRelative
      M spec m F ψ g B₁ J := by
  exact ⟨h.1,
    uniformlyConstitutive_implies_constitutive
      M spec F ψ B₁ J h.2.1,
    h.2.2⟩

theorem groundedUniformPR_implies_uniformGeneralizedPR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsGroundedConfirmatoryUniformPermanssonRegimeRelative
      M spec m F ψ g B₁ J) :
    IsUniformGeneralizedPermanssonRegimeRelative
      M spec m F ψ B₁ J :=
  ⟨h.1.1, h.2.1⟩

end RegimeSpecification

end PermanssonLean
