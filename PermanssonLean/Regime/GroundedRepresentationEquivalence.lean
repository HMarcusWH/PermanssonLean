import PermanssonLean.Regime.GroundedUniformPermansson
import PermanssonLean.Regime.RepresentationEquivalence
import PermanssonLean.Regime.InterventionEquivalence

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH uG uZ uK₁ uK₂

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {G : Type uG} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MeasurableSpace G]
variable [TopologicalSpace S] [TopologicalSpace X]

namespace RegimeSpecification

theorem descriptorLaw_eq_of_inducedKernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (t : ℕ) :
    descriptorLaw M₁ spec μ t =
      descriptorLaw M₂ spec μ t := by
  unfold descriptorLaw
  rw [pathProbability_eq_of_inducedKernel_eq M₁ M₂ hK μ]

theorem descriptorNondegenerate_iff_of_inducedKernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H) :
    IsDescriptorNondegenerate M₁ spec ↔
      IsDescriptorNondegenerate M₂ spec := by
  unfold IsDescriptorNondegenerate
  constructor
  · rintro ⟨y₁, hy₁, t₁, y₂, hy₂, t₂, hne⟩
    refine ⟨y₁, hy₁, t₁, y₂, hy₂, t₂, ?_⟩
    simpa [
      descriptorLaw_eq_of_inducedKernel_eq M₁ M₂ hK spec
        (diracProba y₁) t₁,
      descriptorLaw_eq_of_inducedKernel_eq M₁ M₂ hK spec
        (diracProba y₂) t₂
    ] using hne
  · rintro ⟨y₁, hy₁, t₁, y₂, hy₂, t₂, hne⟩
    refine ⟨y₁, hy₁, t₁, y₂, hy₂, t₂, ?_⟩
    simpa [
      descriptorLaw_eq_of_inducedKernel_eq M₁ M₂ hK spec
        (diracProba y₁) t₁,
      descriptorLaw_eq_of_inducedKernel_eq M₁ M₂ hK spec
        (diracProba y₂) t₂
    ] using hne

theorem confirmatoryGR_iff_of_inducedKernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X)) :
    IsConfirmatoryGeneratedRegime M₁ spec m ↔
      IsConfirmatoryGeneratedRegime M₂ spec m := by
  unfold IsConfirmatoryGeneratedRegime
  rw [
    exactGR_iff_of_inducedKernel_eq M₁ M₂ hK spec m,
    descriptorNondegenerate_iff_of_inducedKernel_eq M₁ M₂ hK spec
  ]

theorem groundedPropertyRelative_iff_of_kernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    {Component₁ : Type uK₁} {Component₂ : Type uK₂}
    (F₁ : InterventionFamily M₁ Component₁)
    (F₂ : InterventionFamily M₂ Component₂)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (J₁ : AdmissibleStrategicIntervention F₁)
    (J₂ : AdmissibleStrategicIntervention F₂)
    (hJ :
      J₁.intervention.apply.inducedKernel =
        J₂.intervention.apply.inducedKernel) :
    IsGroundedPropertyRelative M₁ spec F₁ ψ g J₁ ↔
      IsGroundedPropertyRelative M₂ spec F₂ ψ g J₂ := by
  constructor
  · rintro ⟨ψG, hbase, hinter⟩
    refine ⟨ψG, ?_, ?_⟩
    · intro μ hμ
      have hpath :=
        pathProbability_eq_of_inducedKernel_eq M₁ M₂ hK μ
      simpa [hpath] using hbase μ hμ
    · intro μ hμ
      have hpath :=
        pathProbability_eq_of_inducedKernel_eq
          J₁.intervention.apply J₂.intervention.apply hJ μ
      simpa [hpath] using hinter μ hμ
  · rintro ⟨ψG, hbase, hinter⟩
    refine ⟨ψG, ?_, ?_⟩
    · intro μ hμ
      have hpath :=
        pathProbability_eq_of_inducedKernel_eq M₁ M₂ hK μ
      simpa [hpath] using hbase μ hμ
    · intro μ hμ
      have hpath :=
        pathProbability_eq_of_inducedKernel_eq
          J₁.intervention.apply J₂.intervention.apply hJ μ
      simpa [hpath] using hinter μ hμ

theorem groundedConfirmatoryRelativePR_iff_of_kernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component₁ : Type uK₁} {Component₂ : Type uK₂}
    (F₁ : InterventionFamily M₁ Component₁)
    (F₂ : InterventionFamily M₂ Component₂)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M₁ spec)
    (J₁ : AdmissibleStrategicIntervention F₁)
    (J₂ : AdmissibleStrategicIntervention F₂)
    (hJ :
      J₁.intervention.apply.inducedKernel =
        J₂.intervention.apply.inducedKernel) :
    IsGroundedConfirmatoryPermanssonRegimeRelative
        M₁ spec m F₁ ψ g B₁ J₁ ↔
      IsGroundedConfirmatoryPermanssonRegimeRelative
        M₂ spec m F₂ ψ g
        (B₁.transport M₁ M₂ hK spec) J₂ := by
  unfold IsGroundedConfirmatoryPermanssonRegimeRelative
  rw [
    confirmatoryGR_iff_of_inducedKernel_eq M₁ M₂ hK spec m,
    strategicallyConstitutive_iff_of_kernel_eq
      M₁ M₂ hK spec F₁ F₂ ψ B₁ J₁ J₂ hJ,
    groundedPropertyRelative_iff_of_kernel_eq
      M₁ M₂ hK spec F₁ F₂ ψ g J₁ J₂ hJ
  ]

section Metric

variable [MetricSpace Z]

theorem groundedConfirmatoryUniformRelativePR_iff_of_kernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component₁ : Type uK₁} {Component₂ : Type uK₂}
    (F₁ : InterventionFamily M₁ Component₁)
    (F₂ : InterventionFamily M₂ Component₂)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M₁ spec)
    (J₁ : AdmissibleStrategicIntervention F₁)
    (J₂ : AdmissibleStrategicIntervention F₂)
    (hJ :
      J₁.intervention.apply.inducedKernel =
        J₂.intervention.apply.inducedKernel) :
    IsGroundedConfirmatoryUniformPermanssonRegimeRelative
        M₁ spec m F₁ ψ g B₁ J₁ ↔
      IsGroundedConfirmatoryUniformPermanssonRegimeRelative
        M₂ spec m F₂ ψ g
        (B₁.transport M₁ M₂ hK spec) J₂ := by
  unfold IsGroundedConfirmatoryUniformPermanssonRegimeRelative
  rw [
    confirmatoryGR_iff_of_inducedKernel_eq M₁ M₂ hK spec m,
    uniformlyConstitutive_iff_of_kernel_eq
      M₁ M₂ hK spec F₁ F₂ ψ B₁ J₁ J₂ hJ,
    groundedPropertyRelative_iff_of_kernel_eq
      M₁ M₂ hK spec F₁ F₂ ψ g J₁ J₂ hJ
  ]

end Metric

end RegimeSpecification

end PermanssonLean
