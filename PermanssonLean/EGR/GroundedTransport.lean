import PermanssonLean.EGR.PermanssonTransport
import PermanssonLean.Regime.GroundedUniformPermansson

open MeasureTheory ProbabilityTheory Set

namespace PermanssonLean

universe uX uA uH uZ

namespace PaperISelectedModel

variable {X : Type uX} {A : Type uA} {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace H]
variable [TopologicalSpace X] [TopologicalSpace A]
variable [MeasurableSingletonClass A]
variable [MeasurableSingletonClass (PaperIStrategicState A)]
variable [MeasurableSpace.SeparatesPoints
  (JointState (PaperIStrategicState A) X)]

/-- Paper-I descriptor law at a finite date. -/
noncomputable def paperIDescriptorLaw
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (μ : ProbabilityMeasure X)
    (t : ℕ) :
    ProbabilityMeasure H :=
  (M.pathProbability μ).map
    (fun w => spec.descriptor (w t))

/-- Paper-I confirmatory descriptor nondegeneracy. -/
def IsPaperIDescriptorNondegenerate
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H) : Prop :=
  ∃ x₁ ∈ spec.basin, ∃ t₁ : ℕ,
    ∃ x₂ ∈ spec.basin, ∃ t₂ : ℕ,
      M.paperIDescriptorLaw spec (diracProba x₁) t₁ ≠
        M.paperIDescriptorLaw spec (diracProba x₂) t₂

/-- Confirmatory Paper-I EGR: Paper-I EGR plus basin-reachable descriptor-law
nondegeneracy. -/
def IsPaperIConfirmatoryEGR
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X) : Prop :=
  IsPaperIEGR M spec m ∧
    M.IsPaperIDescriptorNondegenerate spec

/-- The natural grounded relevance map for the already formalized world-path
branch of the Paper-I embedding is simply the world coordinate. -/
noncomputable def worldRelevanceMap
    (spec : RegimeSpecification X H) :
    RegimeSpecification.GroundedRelevanceMap
      (embeddedSpec (A := A) spec) X where
  observe := Prod.snd
  observe_measurable := measurable_snd
  regimeRegion := spec.region
  regimeRegion_measurable := spec.region_measurable
  region_preimage := by
    ext y
    simp [embeddedSpec]
  descriptor := spec.descriptor
  descriptor_measurable := spec.descriptor_measurable
  descriptor_factor := by
    rfl

/-- The transported world-path property globally factors through the natural
world-coordinate relevance map, with the original Paper-I property as ψ_G. -/
theorem transportProperty_globallyGrounded
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : RegimePropertyMap X Z) :
    RegimeSpecification.GloballyFactorsThroughRelevanceMap
      (embeddedSpec (A := A) spec)
      (transportProperty (A := A) ψI)
      (worldRelevanceMap (A := A) spec) where
  groundedProperty := ψI
  factor := by
    intro μ
    rfl

/-- Descriptor laws of the canonical point embedding coincide with the
Paper-I descriptor laws. -/
theorem embedded_descriptorLaw_eq_paperI
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (x : X)
    (t : ℕ) :
    RegimeSpecification.descriptorLaw
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        (diracProba (initialEmbedding (X := X) (A := A) x))
        t =
      M.paperIDescriptorLaw spec (diracProba x) t := by
  unfold RegimeSpecification.descriptorLaw paperIDescriptorLaw
  apply ProbabilityMeasure.toMeasure_injective
  change
    (RegimeSpecification.pathProbability M.embeddedModel
      (diracProba (initialEmbedding (X := X) (A := A) x))).toMeasure.map
        (fun w => spec.descriptor ((w t).2)) =
      (M.pathProbability (diracProba x)).toMeasure.map
        (fun w => spec.descriptor (w t))
  have hproj :=
    M.embedded_worldPathLaw_eq_paperI
      (diracProba (initialEmbedding (X := X) (A := A) x))
  have hwm :
      (diracProba (initialEmbedding (X := X) (A := A) x)).map Prod.snd =
        diracProba x := by
    apply ProbabilityMeasure.toMeasure_injective
    change
      (Measure.dirac (initialEmbedding (X := X) (A := A) x)).map Prod.snd =
        Measure.dirac x
    exact Measure.map_dirac' measurable_snd _
  rw [hwm] at hproj
  change
    (M.embeddedModel.pathLaw
      (diracProba (initialEmbedding (X := X) (A := A) x)).toMeasure).map
        (fun w => spec.descriptor ((w t).2)) =
      (M.pathLaw (diracProba x).toMeasure).map
        (fun w => spec.descriptor (w t))
  have hprojMap := congrArg
    (fun μ : Measure (ℕ → X) =>
      μ.map (fun w => spec.descriptor (w t))) hproj
  rw [Measure.map_map
    (spec.descriptor_measurable.comp (measurable_pi_apply t))
    (worldPathProjection_measurable
      (X := X) (S := PaperIStrategicState A))] at hprojMap
  simpa [worldPathProjection, Function.comp_def] using hprojMap

theorem paperIDescriptorNondegenerate_iff_embedded
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H) :
    M.IsPaperIDescriptorNondegenerate spec ↔
      RegimeSpecification.IsDescriptorNondegenerate
        M.embeddedModel (embeddedSpec (A := A) spec) := by
  constructor
  · rintro ⟨x₁, hx₁, t₁, x₂, hx₂, t₂, hne⟩
    refine ⟨initialEmbedding (X := X) (A := A) x₁,
      ⟨Set.mem_singleton _, hx₁⟩, t₁,
      initialEmbedding (X := X) (A := A) x₂,
      ⟨Set.mem_singleton _, hx₂⟩, t₂, ?_⟩
    simpa [
      M.embedded_descriptorLaw_eq_paperI spec x₁ t₁,
      M.embedded_descriptorLaw_eq_paperI spec x₂ t₂
    ] using hne
  · rintro ⟨y₁, hy₁, t₁, y₂, hy₂, t₂, hne⟩
    rcases y₁ with ⟨s₁, x₁⟩
    rcases y₂ with ⟨s₂, x₂⟩
    have hs₁ : s₁ = initialStrategicState (A := A) :=
      Set.mem_singleton_iff.mp hy₁.1
    have hs₂ : s₂ = initialStrategicState (A := A) :=
      Set.mem_singleton_iff.mp hy₂.1
    subst s₁
    subst s₂
    refine ⟨x₁, hy₁.2, t₁, x₂, hy₂.2, t₂, ?_⟩
    simpa [
      M.embedded_descriptorLaw_eq_paperI spec x₁ t₁,
      M.embedded_descriptorLaw_eq_paperI spec x₂ t₂
    ] using hne

theorem paperIConfirmatoryEGR_iff_embeddedConfirmatoryGR
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X) :
    M.IsPaperIConfirmatoryEGR spec m ↔
      RegimeSpecification.IsConfirmatoryGeneratedRegime
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        (embeddedReferenceMeasure (A := A) m) := by
  unfold IsPaperIConfirmatoryEGR
    RegimeSpecification.IsConfirmatoryGeneratedRegime
  rw [
    M.paperIEGR_iff_embeddedExactGR spec m,
    M.paperIDescriptorNondegenerate_iff_embedded spec
  ]

/-- Paper-I grounded confirmatory PR for the world-path branch. -/
def IsPaperIGroundedPermanssonRegimeRelative
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : Prop :=
  M.IsPaperIConfirmatoryEGR spec m ∧
    IsPaperIConstitutive M spec ψI J B₁

theorem paperIGroundedPermansson_iff_embeddedGroundedConfirmatoryPR
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    M.IsPaperIGroundedPermanssonRegimeRelative spec m ψI J B₁ ↔
      RegimeSpecification.IsGroundedConfirmatoryPermanssonRegimeRelative
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        (embeddedReferenceMeasure (A := A) m)
        (PaperIPolicyIntervention.transportedFamily M)
        (transportProperty (A := A) ψI)
        (worldRelevanceMap (A := A) spec)
        (PaperIComparisonSet.embedded M spec B₁)
        (J.transportedIntervention M) := by
  constructor
  · intro h
    refine ⟨
      (M.paperIConfirmatoryEGR_iff_embeddedConfirmatoryGR spec m).1 h.1,
      (M.paperIConstitutive_iff_embedded spec ψI J B₁).1 h.2,
      ?_⟩
    exact (M.transportProperty_globallyGrounded spec ψI).relative
      M.embeddedModel
      (embeddedSpec (A := A) spec)
      (PaperIPolicyIntervention.transportedFamily M)
      (transportProperty (A := A) ψI)
      (worldRelevanceMap (A := A) spec)
      (J.transportedIntervention M)
  · intro h
    exact ⟨
      (M.paperIConfirmatoryEGR_iff_embeddedConfirmatoryGR spec m).2 h.1,
      (M.paperIConstitutive_iff_embedded spec ψI J B₁).2 h.2.1⟩

section Metric

variable [MetricSpace Z]

def IsPaperIGroundedUniformPermanssonRegimeRelative
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : Prop :=
  M.IsPaperIConfirmatoryEGR spec m ∧
    IsPaperIUniformlyConstitutive M spec ψI J B₁

theorem paperIGroundedUniformPermansson_iff_embeddedGroundedUniformPR
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    M.IsPaperIGroundedUniformPermanssonRegimeRelative
        spec m ψI J B₁ ↔
      RegimeSpecification.IsGroundedConfirmatoryUniformPermanssonRegimeRelative
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        (embeddedReferenceMeasure (A := A) m)
        (PaperIPolicyIntervention.transportedFamily M)
        (transportProperty (A := A) ψI)
        (worldRelevanceMap (A := A) spec)
        (PaperIComparisonSet.embedded M spec B₁)
        (J.transportedIntervention M) := by
  constructor
  · intro h
    refine ⟨
      (M.paperIConfirmatoryEGR_iff_embeddedConfirmatoryGR spec m).1 h.1,
      (M.paperIUniformlyConstitutive_iff_embedded spec ψI J B₁).1 h.2,
      ?_⟩
    exact (M.transportProperty_globallyGrounded spec ψI).relative
      M.embeddedModel
      (embeddedSpec (A := A) spec)
      (PaperIPolicyIntervention.transportedFamily M)
      (transportProperty (A := A) ψI)
      (worldRelevanceMap (A := A) spec)
      (J.transportedIntervention M)
  · intro h
    exact ⟨
      (M.paperIConfirmatoryEGR_iff_embeddedConfirmatoryGR spec m).2 h.1,
      (M.paperIUniformlyConstitutive_iff_embedded spec ψI J B₁).2 h.2.1⟩

end Metric

end PaperISelectedModel

end PermanssonLean
