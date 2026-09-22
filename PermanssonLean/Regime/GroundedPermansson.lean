import PermanssonLean.Regime.GroundedProperty
import PermanssonLean.Regime.Permansson

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH uG uZ uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {G : Type uG} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MeasurableSpace G]
variable [TopologicalSpace S] [TopologicalSpace X]

namespace RegimeSpecification

/-- Grounded generalized PR relative to one frozen constitutive protocol. -/
def IsGroundedPermanssonRegimeRelative
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) : Prop :=
  IsGeneralizedPermanssonRegimeRelative M spec m F ψ B₁ J ∧
    IsGroundedPropertyRelative M spec F ψ g J

/-- Formal grounded confirmatory subclass PR_g: confirmatory GR baseline,
strategic constitution, and grounded property semantics for the same frozen
protocol. -/
def IsGroundedConfirmatoryPermanssonRegimeRelative
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
  IsStrategicallyConstitutive M spec F ψ B₁ J ∧
  IsGroundedPropertyRelative M spec F ψ g J

/-- Family form of the grounded confirmatory subclass. -/
def IsGroundedConfirmatoryPermanssonRegime
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec) : Prop :=
  IsConfirmatoryGeneratedRegime M spec m ∧
  ∃ J : AdmissibleStrategicIntervention F,
    IsStrategicallyConstitutive M spec F ψ B₁ J ∧
    IsGroundedPropertyRelative M spec F ψ g J

theorem groundedPR_implies_generalizedPR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsGroundedPermanssonRegimeRelative M spec m F ψ g B₁ J) :
    IsGeneralizedPermanssonRegimeRelative M spec m F ψ B₁ J :=
  h.1

theorem groundedConfirmatoryPR_confirmatoryGR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsGroundedConfirmatoryPermanssonRegimeRelative
      M spec m F ψ g B₁ J) :
    IsConfirmatoryGeneratedRegime M spec m :=
  h.1

theorem groundedConfirmatoryPR_constitutive
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsGroundedConfirmatoryPermanssonRegimeRelative
      M spec m F ψ g B₁ J) :
    IsStrategicallyConstitutive M spec F ψ B₁ J :=
  h.2.1

theorem groundedConfirmatoryPR_grounded
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsGroundedConfirmatoryPermanssonRegimeRelative
      M spec m F ψ g B₁ J) :
    IsGroundedPropertyRelative M spec F ψ g J :=
  h.2.2

theorem groundedConfirmatoryPR_implies_groundedPR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsGroundedConfirmatoryPermanssonRegimeRelative
      M spec m F ψ g B₁ J) :
    IsGroundedPermanssonRegimeRelative M spec m F ψ g B₁ J := by
  exact ⟨⟨h.1.1, h.2.1⟩, h.2.2⟩

theorem groundedConfirmatoryPR_implies_generalizedPR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsGroundedConfirmatoryPermanssonRegimeRelative
      M spec m F ψ g B₁ J) :
    IsGeneralizedPermanssonRegimeRelative M spec m F ψ B₁ J :=
  (groundedConfirmatoryPR_implies_groundedPR
    M spec m F ψ g B₁ J h).1

theorem groundedConfirmatoryFamily_implies_generalizedPR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (h : IsGroundedConfirmatoryPermanssonRegime M spec m F ψ g B₁) :
    IsGeneralizedPermanssonRegime M spec m F ψ B₁ := by
  rcases h.2 with ⟨J, hJ, hg⟩
  exact ⟨h.1.1, ⟨J, hJ⟩⟩

end RegimeSpecification

end PermanssonLean
