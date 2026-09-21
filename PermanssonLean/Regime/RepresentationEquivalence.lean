import PermanssonLean.Regime.GeneratedRegime
import PermanssonLean.Regime.Constitution

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH uZ

variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
variable [TopologicalSpace S] [TopologicalSpace X]

namespace StrategicWorldModel

/-- Proposition-7.1 bridge: the canonical path law depends on a model only
through its induced joint kernel. -/
theorem pathLaw_eq_of_inducedKernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (μ0 : Measure (JointState S X))
    [IsProbabilityMeasure μ0] :
    M₁.pathLaw μ0 = M₂.pathLaw μ0 := by
  simp [pathLaw, hK]

end StrategicWorldModel

namespace RegimeSpecification

theorem pathProbability_eq_of_inducedKernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (μ0 : ProbabilityMeasure (JointState S X)) :
    pathProbability M₁ μ0 = pathProbability M₂ μ0 := by
  apply ProbabilityMeasure.toMeasure_injective
  exact StrategicWorldModel.pathLaw_eq_of_inducedKernel_eq
    M₁ M₂ hK μ0.toMeasure

theorem baselinePropertyValue_eq_of_inducedKernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (y : JointState S X) :
    baselinePropertyValue ψ M₁ y = baselinePropertyValue ψ M₂ y := by
  unfold baselinePropertyValue
  rw [pathProbability_eq_of_inducedKernel_eq M₁ M₂ hK]

theorem basinPathLawNontrivial_iff_of_inducedKernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H) :
    BasinPathLawNontrivial M₁ spec ↔ BasinPathLawNontrivial M₂ spec := by
  unfold BasinPathLawNontrivial
  constructor <;>
    rintro ⟨y₁, hy₁, y₂, hy₂, hne⟩ <;>
    refine ⟨y₁, hy₁, y₂, hy₂, ?_⟩
  · simpa [
      StrategicWorldModel.pathLaw_eq_of_inducedKernel_eq M₁ M₂ hK
        (Measure.dirac y₁),
      StrategicWorldModel.pathLaw_eq_of_inducedKernel_eq M₁ M₂ hK
        (Measure.dirac y₂)
    ] using hne
  · simpa [
      StrategicWorldModel.pathLaw_eq_of_inducedKernel_eq M₁ M₂ hK
        (Measure.dirac y₁),
      StrategicWorldModel.pathLaw_eq_of_inducedKernel_eq M₁ M₂ hK
        (Measure.dirac y₂)
    ] using hne

theorem assumption41_iff_of_inducedKernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X)) :
    Assumption41 M₁ spec m ↔ Assumption41 M₂ spec m := by
  unfold Assumption41
  rw [basinPathLawNontrivial_iff_of_inducedKernel_eq M₁ M₂ hK spec]

theorem exactInvariant_iff_of_inducedKernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H) :
    IsExactlyInvariant M₁ spec ↔ IsExactlyInvariant M₂ spec := by
  unfold IsExactlyInvariant
  rw [hK]

theorem limitingOccupation_iff_of_inducedKernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (initLaw : ProbabilityMeasure (JointState S X)) :
    IsLimitingOccupationLaw M₁ spec initLaw ↔
      IsLimitingOccupationLaw M₂ spec initLaw := by
  unfold IsLimitingOccupationLaw
  rw [StrategicWorldModel.pathLaw_eq_of_inducedKernel_eq
    M₁ M₂ hK initLaw.toMeasure]

/-- Proposition 7.1: for a fixed regime specification and reference measure,
Exact-GR status is representation invariant under equality of the induced
joint kernel. -/
theorem exactGR_iff_of_inducedKernel_eq
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X)) :
    IsExactGeneratedRegime M₁ spec m ↔
      IsExactGeneratedRegime M₂ spec m := by
  constructor
  · intro h
    refine ⟨canonicalProcessWellPosed M₂, ?_, ?_, ?_⟩
    · exact (assumption41_iff_of_inducedKernel_eq M₁ M₂ hK spec m).1 h.2.1
    · exact (exactInvariant_iff_of_inducedKernel_eq M₁ M₂ hK spec).1 h.2.2.1
    · intro initLaw hinit
      exact (limitingOccupation_iff_of_inducedKernel_eq
        M₁ M₂ hK spec initLaw).1 (h.2.2.2 initLaw hinit)
  · intro h
    refine ⟨canonicalProcessWellPosed M₁, ?_, ?_, ?_⟩
    · exact (assumption41_iff_of_inducedKernel_eq M₁ M₂ hK spec m).2 h.2.1
    · exact (exactInvariant_iff_of_inducedKernel_eq M₁ M₂ hK spec).2 h.2.2.1
    · intro initLaw hinit
      exact (limitingOccupation_iff_of_inducedKernel_eq
        M₁ M₂ hK spec initLaw).2 (h.2.2.2 initLaw hinit)

/-- Transport the same frozen B₁ state set and certificates across a
representation change with the same induced joint kernel. -/
noncomputable def ConstitutiveComparisonSet.transport
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (B₁ : ConstitutiveComparisonSet M₁ spec) :
    ConstitutiveComparisonSet M₂ spec where
  states := B₁.states
  states_measurable := B₁.states_measurable
  states_subset_basin := B₁.states_subset_basin
  pathLawNontrivial := by
    rcases B₁.pathLawNontrivial with ⟨y₁, hy₁, y₂, hy₂, hne⟩
    refine ⟨y₁, hy₁, y₂, hy₂, ?_⟩
    simpa [
      StrategicWorldModel.pathLaw_eq_of_inducedKernel_eq M₁ M₂ hK
        (Measure.dirac y₁),
      StrategicWorldModel.pathLaw_eq_of_inducedKernel_eq M₁ M₂ hK
        (Measure.dirac y₂)
    ] using hne

@[simp]
theorem ConstitutiveComparisonSet.transport_states
    (M₁ M₂ : StrategicWorldModel S X A)
    (hK : M₁.inducedKernel = M₂.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (B₁ : ConstitutiveComparisonSet M₁ spec) :
    (B₁.transport M₁ M₂ hK spec).states = B₁.states :=
  rfl

end RegimeSpecification

end PermanssonLean
