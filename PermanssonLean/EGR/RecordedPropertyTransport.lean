import PermanssonLean.EGR.ActionDecode

open MeasureTheory ProbabilityTheory Set

namespace PermanssonLean

universe uX uA uH uZ

/-- Action-sensitive Paper-I property map on decoded execution laws. -/
abbrev PaperIRecordedPropertyMap
    (X : Type uX) (A : Type uA) (Z : Type uZ)
    [MeasurableSpace X] [MeasurableSpace A] :=
  ProbabilityMeasure (PaperIDecodedPath X A) → Z

namespace PaperISelectedModel

variable {X : Type uX} {A : Type uA} {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace H]
variable [TopologicalSpace X] [TopologicalSpace A]
variable [MeasurableSingletonClass A]
variable [MeasurableSingletonClass (PaperIStrategicState A)]
variable [MeasurableSpace.SeparatesPoints
  (JointState (PaperIStrategicState A) X)]
variable [Inhabited A]

/-- Transport an action-sensitive Paper-I property by the Section-6.2 decoder D. -/
noncomputable def transportRecordedProperty
    (M : PaperISelectedModel X A)
    (ψI : PaperIRecordedPropertyMap X A Z) :
    RegimePropertyMap
      (JointState (PaperIStrategicState A) X) Z :=
  fun μ => ψI (μ.map (recordedDecode (X := X) (A := A)))

/-- Decoded baseline Paper-I property value. -/
noncomputable def paperIRecordedBaselinePropertyValue
    (M : PaperISelectedModel X A)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (x : X) : Z :=
  ψI (M.recordedPathProbability x)

/-- Decoded intervention Paper-I property value. -/
noncomputable def paperIRecordedIntervenedPropertyValue
    (M : PaperISelectedModel X A)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (x : X) : Z :=
  ψI (M.recordedCounterfactualPathProbability J x)

theorem transported_recorded_baselinePropertyValue_eq
    (M : PaperISelectedModel X A)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (x : X) :
    RegimeSpecification.baselinePropertyValue
        (M.transportRecordedProperty ψI)
        M.embeddedModel
        (initialEmbedding (X := X) (A := A) x) =
      M.paperIRecordedBaselinePropertyValue ψI x := by
  rfl

theorem transported_recorded_intervenedPropertyValue_eq
    (M : PaperISelectedModel X A)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (x : X) :
    RegimeSpecification.intervenedPropertyValue
        (M.transportRecordedProperty ψI)
        (J.transportedIntervention M).intervention
        (initialEmbedding (X := X) (A := A) x) =
      M.paperIRecordedIntervenedPropertyValue ψI J x := by
  rfl

/-- Paper-I constitutive criterion for an action-sensitive property. -/
def IsPaperIRecordedConstitutive
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : Prop :=
  ∀ x ∈ B₁.states,
    M.paperIRecordedBaselinePropertyValue ψI x ≠
      M.paperIRecordedIntervenedPropertyValue ψI J x

theorem paperIRecordedConstitutive_iff_embedded
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    IsPaperIRecordedConstitutive M spec ψI J B₁ ↔
      RegimeSpecification.IsStrategicallyConstitutive
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        (PaperIPolicyIntervention.transportedFamily M)
        (M.transportRecordedProperty ψI)
        (PaperIComparisonSet.embedded M spec B₁)
        (J.transportedIntervention M) := by
  constructor
  · intro h y hy
    rcases y with ⟨s, x⟩
    have hs :
        s = initialStrategicState (A := A) :=
      Set.mem_singleton_iff.mp hy.1
    subst s
    change
      RegimeSpecification.baselinePropertyValue
          (M.transportRecordedProperty ψI)
          M.embeddedModel
          (initialEmbedding (X := X) (A := A) x) ≠
        RegimeSpecification.intervenedPropertyValue
          (M.transportRecordedProperty ψI)
          (J.transportedIntervention M).intervention
          (initialEmbedding (X := X) (A := A) x)
    rw [
      M.transported_recorded_baselinePropertyValue_eq ψI x,
      M.transported_recorded_intervenedPropertyValue_eq ψI J x
    ]
    exact h x hy.2
  · intro h x hx
    have hy :
        (initialEmbedding (X := X) (A := A) x) ∈
          (PaperIComparisonSet.embedded M spec B₁).states :=
      ⟨Set.mem_singleton _, hx⟩
    have hh := h (initialEmbedding (X := X) (A := A) x) hy
    change
      RegimeSpecification.baselinePropertyValue
          (M.transportRecordedProperty ψI)
          M.embeddedModel
          (initialEmbedding (X := X) (A := A) x) ≠
        RegimeSpecification.intervenedPropertyValue
          (M.transportRecordedProperty ψI)
          (J.transportedIntervention M).intervention
          (initialEmbedding (X := X) (A := A) x) at hh
    rw [
      M.transported_recorded_baselinePropertyValue_eq ψI x,
      M.transported_recorded_intervenedPropertyValue_eq ψI J x
    ] at hh
    exact hh

def IsPaperIRecordedPermanssonRegimeRelative
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : Prop :=
  IsPaperIEGR M spec m ∧
    IsPaperIRecordedConstitutive M spec ψI J B₁

theorem paperIRecordedPermansson_iff_embeddedRelativePR
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    IsPaperIRecordedPermanssonRegimeRelative
        M spec m ψI J B₁ ↔
      RegimeSpecification.IsGeneralizedPermanssonRegimeRelative
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        (embeddedReferenceMeasure (A := A) m)
        (PaperIPolicyIntervention.transportedFamily M)
        (M.transportRecordedProperty ψI)
        (PaperIComparisonSet.embedded M spec B₁)
        (J.transportedIntervention M) := by
  unfold IsPaperIRecordedPermanssonRegimeRelative
    RegimeSpecification.IsGeneralizedPermanssonRegimeRelative
  rw [
    M.paperIEGR_iff_embeddedExactGR spec m,
    M.paperIRecordedConstitutive_iff_embedded spec ψI J B₁
  ]

section Metric

variable [MetricSpace Z]

noncomputable def paperIRecordedConstitutiveEffect
    (M : PaperISelectedModel X A)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (x : X) : ℝ :=
  dist
    (M.paperIRecordedBaselinePropertyValue ψI x)
    (M.paperIRecordedIntervenedPropertyValue ψI J x)

noncomputable def paperIRecordedConstitutiveMargin
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : ℝ :=
  sInf (M.paperIRecordedConstitutiveEffect ψI J '' B₁.states)

def IsPaperIRecordedUniformlyConstitutive
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : Prop :=
  0 < M.paperIRecordedConstitutiveMargin spec ψI J B₁

theorem transported_recorded_constitutiveEffect_eq
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec)
    (x : X) :
    M.paperIRecordedConstitutiveEffect ψI J x =
      RegimeSpecification.constitutiveEffect
        M.embeddedModel
        (M.transportRecordedProperty ψI)
        (J.transportedIntervention M)
        (initialEmbedding (X := X) (A := A) x) := by
  unfold paperIRecordedConstitutiveEffect
    RegimeSpecification.constitutiveEffect
  rw [
    M.transported_recorded_baselinePropertyValue_eq ψI x,
    M.transported_recorded_intervenedPropertyValue_eq ψI J x
  ]

theorem paperIRecordedConstitutiveMargin_eq_embedded
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    M.paperIRecordedConstitutiveMargin spec ψI J B₁ =
      RegimeSpecification.constitutiveMargin
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        (PaperIPolicyIntervention.transportedFamily M)
        (M.transportRecordedProperty ψI)
        (PaperIComparisonSet.embedded M spec B₁)
        (J.transportedIntervention M) := by
  unfold paperIRecordedConstitutiveMargin
    RegimeSpecification.constitutiveMargin
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨initialEmbedding (X := X) (A := A) x,
      ⟨Set.mem_singleton _, hx⟩, ?_⟩
    exact (M.transported_recorded_constitutiveEffect_eq
      spec ψI J B₁ x).symm
  · rintro ⟨y, hy, rfl⟩
    rcases y with ⟨s, x⟩
    have hs :
        s = initialStrategicState (A := A) :=
      Set.mem_singleton_iff.mp hy.1
    subst s
    refine ⟨x, hy.2, ?_⟩
    exact M.transported_recorded_constitutiveEffect_eq
      spec ψI J B₁ x

theorem paperIRecordedUniformlyConstitutive_iff_embedded
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    IsPaperIRecordedUniformlyConstitutive M spec ψI J B₁ ↔
      RegimeSpecification.IsUniformlyStrategicallyConstitutive
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        (PaperIPolicyIntervention.transportedFamily M)
        (M.transportRecordedProperty ψI)
        (PaperIComparisonSet.embedded M spec B₁)
        (J.transportedIntervention M) := by
  unfold IsPaperIRecordedUniformlyConstitutive
  rw [
    RegimeSpecification.uniformlyConstitutive_iff_margin_pos,
    M.paperIRecordedConstitutiveMargin_eq_embedded spec ψI J B₁
  ]

def IsPaperIRecordedUniformPermanssonRegimeRelative
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : Prop :=
  IsPaperIEGR M spec m ∧
    IsPaperIRecordedUniformlyConstitutive M spec ψI J B₁

theorem paperIRecordedUniformPermansson_iff_embeddedRelativePR
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    IsPaperIRecordedUniformPermanssonRegimeRelative
        M spec m ψI J B₁ ↔
      RegimeSpecification.IsUniformGeneralizedPermanssonRegimeRelative
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        (embeddedReferenceMeasure (A := A) m)
        (PaperIPolicyIntervention.transportedFamily M)
        (M.transportRecordedProperty ψI)
        (PaperIComparisonSet.embedded M spec B₁)
        (J.transportedIntervention M) := by
  unfold IsPaperIRecordedUniformPermanssonRegimeRelative
    RegimeSpecification.IsUniformGeneralizedPermanssonRegimeRelative
  rw [
    M.paperIEGR_iff_embeddedExactGR spec m,
    M.paperIRecordedUniformlyConstitutive_iff_embedded spec ψI J B₁
  ]

end Metric

end PaperISelectedModel

end PermanssonLean
