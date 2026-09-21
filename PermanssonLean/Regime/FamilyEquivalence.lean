import PermanssonLean.Intervention.Signature
import PermanssonLean.Regime.InterventionEquivalence
import PermanssonLean.Regime.UniformPermansson

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH uZ uK uL₁ uL₂

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
variable [TopologicalSpace S] [TopologicalSpace X]

namespace RegimeSpecification

/-- Positive PR witness scoped to one explicitly frozen intervention family. -/
def HasConstitutiveWitnessInFrozenFamily
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK} {Label : Type uL₁}
    (F : InterventionFamily M Component)
    (J : FrozenStrategicInterventionFamily F Label)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) : Prop :=
  ∃ l : Label,
    IsStrategicallyConstitutive M spec F ψ B₁ (J.intervention l)

/-- Protocol-scoped negative certificate.  This means no witness exists in
this declared frozen family, not that no conceivable intervention can ever be
constitutive. -/
def NoConstitutiveWitnessInFrozenFamily
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK} {Label : Type uL₁}
    (F : InterventionFamily M Component)
    (J : FrozenStrategicInterventionFamily F Label)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) : Prop :=
  ∀ l : Label,
    ¬ IsStrategicallyConstitutive M spec F ψ B₁ (J.intervention l)

/-- Generalized PR classification explicitly scoped to a frozen intervention
family. -/
def IsFrozenFamilyPermanssonRegime
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK} {Label : Type uL₁}
    (F : InterventionFamily M Component)
    (J : FrozenStrategicInterventionFamily F Label)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) : Prop :=
  IsExactGeneratedRegime M spec m ∧
    HasConstitutiveWitnessInFrozenFamily M spec F J ψ B₁

theorem familyEquivalence_baselineKernel_eq
    {M₁ M₂ : StrategicWorldModel S X A}
    {Component₁ Component₂ : Type uK}
    {Label₁ : Type uL₁} {Label₂ : Type uL₂}
    {F₁ : InterventionFamily M₁ Component₁}
    {F₂ : InterventionFamily M₂ Component₂}
    {J₁ : FrozenStrategicInterventionFamily F₁ Label₁}
    {J₂ : FrozenStrategicInterventionFamily F₂ Label₂}
    (E : InterventionCompatibleFamilyEquivalence F₁ F₂ J₁ J₂) :
    M₁.inducedKernel = M₂.inducedKernel :=
  E.signatures_match.1

theorem familyEquivalence_intervenedKernel_eq
    {M₁ M₂ : StrategicWorldModel S X A}
    {Component₁ Component₂ : Type uK}
    {Label₁ : Type uL₁} {Label₂ : Type uL₂}
    {F₁ : InterventionFamily M₁ Component₁}
    {F₂ : InterventionFamily M₂ Component₂}
    {J₁ : FrozenStrategicInterventionFamily F₁ Label₁}
    {J₂ : FrozenStrategicInterventionFamily F₂ Label₂}
    (E : InterventionCompatibleFamilyEquivalence F₁ F₂ J₁ J₂)
    (l : Label₁) :
    (J₁.intervention l).intervention.apply.inducedKernel =
      (J₂.intervention (E.matching.labelEquiv l)).intervention.apply.inducedKernel :=
  E.signatures_match.2 l

/-- Proposition 7.4a, positive-witness form. -/
theorem hasConstitutiveWitness_iff_of_familyEquivalence
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
    HasConstitutiveWitnessInFrozenFamily M₁ spec F₁ J₁ ψ B₁ ↔
      HasConstitutiveWitnessInFrozenFamily M₂ spec F₂ J₂ ψ
        (B₁.transport M₁ M₂ (familyEquivalence_baselineKernel_eq E) spec) := by
  let φ := E.matching.labelEquiv
  have hK := familyEquivalence_baselineKernel_eq E
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨φ l, ?_⟩
    exact (strategicallyConstitutive_iff_of_kernel_eq
      M₁ M₂ hK spec F₁ F₂ ψ B₁
      (J₁.intervention l) (J₂.intervention (φ l))
      (familyEquivalence_intervenedKernel_eq E l)).1 hl
  · rintro ⟨l₂, hl₂⟩
    let l₁ : Label₁ := φ.symm l₂
    have hJ :
        (J₁.intervention l₁).intervention.apply.inducedKernel =
          (J₂.intervention l₂).intervention.apply.inducedKernel := by
      simpa [l₁, φ] using familyEquivalence_intervenedKernel_eq E l₁
    refine ⟨l₁, ?_⟩
    exact (strategicallyConstitutive_iff_of_kernel_eq
      M₁ M₂ hK spec F₁ F₂ ψ B₁
      (J₁.intervention l₁) (J₂.intervention l₂) hJ).2 hl₂

/-- Proposition 7.4a, protocol-scoped negative form. -/
theorem noConstitutiveWitness_iff_of_familyEquivalence
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
        (B₁.transport M₁ M₂ (familyEquivalence_baselineKernel_eq E) spec) := by
  rw [NoConstitutiveWitnessInFrozenFamily, NoConstitutiveWitnessInFrozenFamily]
  constructor
  · intro h l₂ h₂
    let φ := E.matching.labelEquiv
    let l₁ : Label₁ := φ.symm l₂
    have hJ :
        (J₁.intervention l₁).intervention.apply.inducedKernel =
          (J₂.intervention l₂).intervention.apply.inducedKernel := by
      simpa [l₁, φ] using familyEquivalence_intervenedKernel_eq E l₁
    exact h l₁ ((strategicallyConstitutive_iff_of_kernel_eq
      M₁ M₂ (familyEquivalence_baselineKernel_eq E) spec
      F₁ F₂ ψ B₁
      (J₁.intervention l₁) (J₂.intervention l₂) hJ).2 h₂)
  · intro h l₁ h₁
    let φ := E.matching.labelEquiv
    exact h (φ l₁) ((strategicallyConstitutive_iff_of_kernel_eq
      M₁ M₂ (familyEquivalence_baselineKernel_eq E) spec
      F₁ F₂ ψ B₁
      (J₁.intervention l₁) (J₂.intervention (φ l₁))
      (familyEquivalence_intervenedKernel_eq E l₁)).1 h₁)

/-- Exact-GR plus frozen-family PR classification is invariant under a
signature match.  This does not make any claim about admissible interventions
outside the frozen family. -/
theorem frozenFamilyPR_iff_of_signature_match
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
    (B₁ : ConstitutiveComparisonSet M₁ spec) :
    IsFrozenFamilyPermanssonRegime M₁ spec m F₁ J₁ ψ B₁ ↔
      IsFrozenFamilyPermanssonRegime M₂ spec m F₂ J₂ ψ
        (B₁.transport M₁ M₂ (familyEquivalence_baselineKernel_eq E) spec) := by
  unfold IsFrozenFamilyPermanssonRegime
  rw [
    exactGR_iff_of_inducedKernel_eq
      M₁ M₂ (familyEquivalence_baselineKernel_eq E) spec m,
    hasConstitutiveWitness_iff_of_familyEquivalence
      M₁ M₂ spec F₁ F₂ J₁ J₂ E ψ B₁
  ]

section Metric

variable [MetricSpace Z]

def HasUniformConstitutiveWitnessInFrozenFamily
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK} {Label : Type uL₁}
    (F : InterventionFamily M Component)
    (J : FrozenStrategicInterventionFamily F Label)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) : Prop :=
  ∃ l : Label,
    IsUniformlyStrategicallyConstitutive M spec F ψ B₁ (J.intervention l)

def IsFrozenFamilyUniformPermanssonRegime
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK} {Label : Type uL₁}
    (F : InterventionFamily M Component)
    (J : FrozenStrategicInterventionFamily F Label)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) : Prop :=
  IsExactGeneratedRegime M spec m ∧
    HasUniformConstitutiveWitnessInFrozenFamily M spec F J ψ B₁

theorem hasUniformConstitutiveWitness_iff_of_familyEquivalence
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
    HasUniformConstitutiveWitnessInFrozenFamily M₁ spec F₁ J₁ ψ B₁ ↔
      HasUniformConstitutiveWitnessInFrozenFamily M₂ spec F₂ J₂ ψ
        (B₁.transport M₁ M₂ (familyEquivalence_baselineKernel_eq E) spec) := by
  let φ := E.matching.labelEquiv
  have hK := familyEquivalence_baselineKernel_eq E
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨φ l, ?_⟩
    exact (uniformlyConstitutive_iff_of_kernel_eq
      M₁ M₂ hK spec F₁ F₂ ψ B₁
      (J₁.intervention l) (J₂.intervention (φ l))
      (familyEquivalence_intervenedKernel_eq E l)).1 hl
  · rintro ⟨l₂, hl₂⟩
    let l₁ : Label₁ := φ.symm l₂
    have hJ :
        (J₁.intervention l₁).intervention.apply.inducedKernel =
          (J₂.intervention l₂).intervention.apply.inducedKernel := by
      simpa [l₁, φ] using familyEquivalence_intervenedKernel_eq E l₁
    refine ⟨l₁, ?_⟩
    exact (uniformlyConstitutive_iff_of_kernel_eq
      M₁ M₂ hK spec F₁ F₂ ψ B₁
      (J₁.intervention l₁) (J₂.intervention l₂) hJ).2 hl₂

theorem frozenFamilyUniformPR_iff_of_signature_match
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
    (B₁ : ConstitutiveComparisonSet M₁ spec) :
    IsFrozenFamilyUniformPermanssonRegime M₁ spec m F₁ J₁ ψ B₁ ↔
      IsFrozenFamilyUniformPermanssonRegime M₂ spec m F₂ J₂ ψ
        (B₁.transport M₁ M₂ (familyEquivalence_baselineKernel_eq E) spec) := by
  unfold IsFrozenFamilyUniformPermanssonRegime
  rw [
    exactGR_iff_of_inducedKernel_eq
      M₁ M₂ (familyEquivalence_baselineKernel_eq E) spec m,
    hasUniformConstitutiveWitness_iff_of_familyEquivalence
      M₁ M₂ spec F₁ F₂ J₁ J₂ E ψ B₁
  ]

end Metric

end RegimeSpecification

end PermanssonLean
