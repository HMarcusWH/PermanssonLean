import PermanssonLean.Regime.GroundedRepresentationEquivalence
import PermanssonLean.Regime.FamilyEquivalence

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH uG uZ uK uL₁ uL₂

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {G : Type uG} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MeasurableSpace G]
variable [TopologicalSpace S] [TopologicalSpace X]

namespace RegimeSpecification

/-- One frozen grounded property semantics shared across an entire declared
intervention family.  This prevents choosing a different ψ_G after seeing
which intervention label is being evaluated. -/
def GroundedFrozenFamilyProperty
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK} {Label : Type uL₁}
    (F : InterventionFamily M Component)
    (J : FrozenStrategicInterventionFamily F Label)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G) : Prop :=
  ∃ ψG : RegimePropertyMap G Z,
    (∀ μ : ProbabilityMeasure (JointState S X),
      IsAdmissibleInitialLaw spec μ →
        ψ (pathProbability M μ) =
          ψG (g.pushPath (pathProbability M μ))) ∧
    (∀ l : Label,
      ∀ μ : ProbabilityMeasure (JointState S X),
        IsAdmissibleInitialLaw spec μ →
          ψ (pathProbability (J.intervention l).intervention.apply μ) =
            ψG (g.pushPath
              (pathProbability (J.intervention l).intervention.apply μ)))

theorem GroundedFrozenFamilyProperty.relative
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK} {Label : Type uL₁}
    (F : InterventionFamily M Component)
    (J : FrozenStrategicInterventionFamily F Label)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (h : GroundedFrozenFamilyProperty M spec F J ψ g)
    (l : Label) :
    IsGroundedPropertyRelative M spec F ψ g (J.intervention l) := by
  rcases h with ⟨ψG, hbase, hinter⟩
  exact ⟨ψG, hbase, hinter l⟩

/-- Confirmatory grounded PR classification scoped to one frozen family. -/
def IsGroundedFrozenFamilyPermanssonRegime
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK} {Label : Type uL₁}
    (F : InterventionFamily M Component)
    (J : FrozenStrategicInterventionFamily F Label)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec) : Prop :=
  IsConfirmatoryGeneratedRegime M spec m ∧
  GroundedFrozenFamilyProperty M spec F J ψ g ∧
  HasConstitutiveWitnessInFrozenFamily M spec F J ψ B₁

theorem groundedFrozenFamilyProperty_iff_of_familyEquivalence
    (M₁ M₂ : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component₁ Component₂ : Type uK}
    {Label₁ : Type uL₁} {Label₂ : Type uL₂}
    (F₁ : InterventionFamily M₁ Component₁)
    (F₂ : InterventionFamily M₂ Component₂)
    (J₁ : FrozenStrategicInterventionFamily F₁ Label₁)
    (J₂ : FrozenStrategicInterventionFamily F₂ Label₂)
    (E : InterventionCompatibleFamilyEquivalence F₁ F₂ J₁ J₂)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G) :
    GroundedFrozenFamilyProperty M₁ spec F₁ J₁ ψ g ↔
      GroundedFrozenFamilyProperty M₂ spec F₂ J₂ ψ g := by
  let φ := E.matching.labelEquiv
  have hK := familyEquivalence_baselineKernel_eq E
  constructor
  · rintro ⟨ψG, hbase, hinter⟩
    refine ⟨ψG, ?_, ?_⟩
    · intro μ hμ
      have hp := pathProbability_eq_of_inducedKernel_eq M₁ M₂ hK μ
      simpa [hp] using hbase μ hμ
    · intro l₂ μ hμ
      let l₁ : Label₁ := φ.symm l₂
      have hJ :
          (J₁.intervention l₁).intervention.apply.inducedKernel =
            (J₂.intervention l₂).intervention.apply.inducedKernel := by
        simpa [l₁, φ] using familyEquivalence_intervenedKernel_eq E l₁
      have hp := pathProbability_eq_of_inducedKernel_eq
        (J₁.intervention l₁).intervention.apply
        (J₂.intervention l₂).intervention.apply hJ μ
      simpa [l₁, hp] using hinter l₁ μ hμ
  · rintro ⟨ψG, hbase, hinter⟩
    refine ⟨ψG, ?_, ?_⟩
    · intro μ hμ
      have hp := pathProbability_eq_of_inducedKernel_eq M₁ M₂ hK μ
      simpa [hp] using hbase μ hμ
    · intro l₁ μ hμ
      have hJ := familyEquivalence_intervenedKernel_eq E l₁
      have hp := pathProbability_eq_of_inducedKernel_eq
        (J₁.intervention l₁).intervention.apply
        (J₂.intervention (φ l₁)).intervention.apply hJ μ
      simpa [hp] using hinter (φ l₁) μ hμ

theorem groundedFrozenFamilyPR_iff_of_signature_match
    (M₁ M₂ : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component₁ Component₂ : Type uK}
    {Label₁ : Type uL₁} {Label₂ : Type uL₂}
    (F₁ : InterventionFamily M₁ Component₁)
    (F₂ : InterventionFamily M₂ Component₂)
    (J₁ : FrozenStrategicInterventionFamily F₁ Label₁)
    (J₂ : FrozenStrategicInterventionFamily F₂ Label₂)
    (E : InterventionCompatibleFamilyEquivalence F₁ F₂ J₁ J₂)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M₁ spec) :
    IsGroundedFrozenFamilyPermanssonRegime
        M₁ spec m F₁ J₁ ψ g B₁ ↔
      IsGroundedFrozenFamilyPermanssonRegime
        M₂ spec m F₂ J₂ ψ g
        (B₁.transport M₁ M₂
          (familyEquivalence_baselineKernel_eq E) spec) := by
  unfold IsGroundedFrozenFamilyPermanssonRegime
  rw [
    confirmatoryGR_iff_of_inducedKernel_eq
      M₁ M₂ (familyEquivalence_baselineKernel_eq E) spec m,
    groundedFrozenFamilyProperty_iff_of_familyEquivalence
      M₁ M₂ spec F₁ F₂ J₁ J₂ E ψ g,
    hasConstitutiveWitness_iff_of_familyEquivalence
      M₁ M₂ spec F₁ F₂ J₁ J₂ E ψ B₁
  ]

theorem groundedFrozenFamily_noWitness_iff_of_signature_match
    (M₁ M₂ : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component₁ Component₂ : Type uK}
    {Label₁ : Type uL₁} {Label₂ : Type uL₂}
    (F₁ : InterventionFamily M₁ Component₁)
    (F₂ : InterventionFamily M₂ Component₂)
    (J₁ : FrozenStrategicInterventionFamily F₁ Label₁)
    (J₂ : FrozenStrategicInterventionFamily F₂ Label₂)
    (E : InterventionCompatibleFamilyEquivalence F₁ F₂ J₁ J₂)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M₁ spec) :
    NoConstitutiveWitnessInFrozenFamily M₁ spec F₁ J₁ ψ B₁ ↔
      NoConstitutiveWitnessInFrozenFamily M₂ spec F₂ J₂ ψ
        (B₁.transport M₁ M₂
          (familyEquivalence_baselineKernel_eq E) spec) :=
  noConstitutiveWitness_iff_of_familyEquivalence
    M₁ M₂ spec F₁ F₂ J₁ J₂ E ψ B₁

section Metric

variable [MetricSpace Z]

def IsGroundedFrozenFamilyUniformPermanssonRegime
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK} {Label : Type uL₁}
    (F : InterventionFamily M Component)
    (J : FrozenStrategicInterventionFamily F Label)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec) : Prop :=
  IsConfirmatoryGeneratedRegime M spec m ∧
  GroundedFrozenFamilyProperty M spec F J ψ g ∧
  HasUniformConstitutiveWitnessInFrozenFamily M spec F J ψ B₁

theorem groundedFrozenFamilyUniformPR_iff_of_signature_match
    (M₁ M₂ : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component₁ Component₂ : Type uK}
    {Label₁ : Type uL₁} {Label₂ : Type uL₂}
    (F₁ : InterventionFamily M₁ Component₁)
    (F₂ : InterventionFamily M₂ Component₂)
    (J₁ : FrozenStrategicInterventionFamily F₁ Label₁)
    (J₂ : FrozenStrategicInterventionFamily F₂ Label₂)
    (E : InterventionCompatibleFamilyEquivalence F₁ F₂ J₁ J₂)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M₁ spec) :
    IsGroundedFrozenFamilyUniformPermanssonRegime
        M₁ spec m F₁ J₁ ψ g B₁ ↔
      IsGroundedFrozenFamilyUniformPermanssonRegime
        M₂ spec m F₂ J₂ ψ g
        (B₁.transport M₁ M₂
          (familyEquivalence_baselineKernel_eq E) spec) := by
  unfold IsGroundedFrozenFamilyUniformPermanssonRegime
  rw [
    confirmatoryGR_iff_of_inducedKernel_eq
      M₁ M₂ (familyEquivalence_baselineKernel_eq E) spec m,
    groundedFrozenFamilyProperty_iff_of_familyEquivalence
      M₁ M₂ spec F₁ F₂ J₁ J₂ E ψ g,
    hasUniformConstitutiveWitness_iff_of_familyEquivalence
      M₁ M₂ spec F₁ F₂ J₁ J₂ E ψ B₁
  ]

end Metric

end RegimeSpecification

end PermanssonLean
