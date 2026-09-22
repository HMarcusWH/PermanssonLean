import PermanssonLean.EGR.RecordedPropertyTransport

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
variable [Inhabited A]

/-- Relevance map for Paper-I properties that actually use the recorded action.
It exposes exactly the world coordinate and action record, but not the clock. -/
noncomputable def worldActionRecordRelevanceMap
    (spec : RegimeSpecification X H) :
    RegimeSpecification.GroundedRelevanceMap
      (embeddedSpec (A := A) spec)
      (X × PaperIActionRecord A) where
  observe := fun y => (y.2, y.1.2)
  observe_measurable :=
    measurable_snd.prodMk (measurable_snd.comp measurable_fst)
  regimeRegion := spec.region ×ˢ Set.univ
  regimeRegion_measurable :=
    spec.region_measurable.prod MeasurableSet.univ
  region_preimage := by
    ext y
    simp [embeddedSpec]
  descriptor := fun z => spec.descriptor z.1
  descriptor_measurable :=
    spec.descriptor_measurable.comp measurable_fst
  descriptor_factor := by
    rfl

/-- Decode a relevance path carrying world state plus the previous-action
record.  The action at t is the record visible at t+1. -/
def decodeRelevantPath :
    (ℕ → X × PaperIActionRecord A) →
      PaperIDecodedPath X A :=
  fun w =>
    (fun t => (w t).1,
      fun t => decodeActionRecord ((w (t + 1)).2))

theorem decodeRelevantPath_measurable :
    Measurable (decodeRelevantPath (X := X) (A := A)) := by
  have hworld :
      Measurable
        (fun w : ℕ → X × PaperIActionRecord A =>
          fun t => (w t).1) := by
    refine Measurable.of_eval fun t => ?_
    exact measurable_fst.comp (measurable_pi_apply t)
  have haction :
      Measurable
        (fun w : ℕ → X × PaperIActionRecord A =>
          fun t => decodeActionRecord ((w (t + 1)).2)) := by
    refine Measurable.of_eval fun t => ?_
    exact decodeActionRecord_measurable.comp
      (measurable_snd.comp (measurable_pi_apply (t + 1)))
  exact hworld.prodMk haction

theorem recordedDecode_factor_relevancePath
    (spec : RegimeSpecification X H)
    (w : ℕ → JointState (PaperIStrategicState A) X) :
    recordedDecode (X := X) (A := A) w =
      decodeRelevantPath
        ((worldActionRecordRelevanceMap (A := A) spec).pathMap w) := by
  apply Prod.ext
  · funext t
    rfl
  · funext t
    rfl

/-- Every recorded-action property factors globally through the relevance
path (x_t, previous-action-record_t). -/
noncomputable def transportRecordedProperty_globallyGrounded
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : PaperIRecordedPropertyMap X A Z) :
    RegimeSpecification.GloballyFactorsThroughRelevanceMap
      (embeddedSpec (A := A) spec)
      (M.transportRecordedProperty ψI)
      (worldActionRecordRelevanceMap (A := A) spec) where
  groundedProperty :=
    fun μ => ψI (μ.map (decodeRelevantPath (X := X) (A := A)))
  factor := by
    intro μ
    unfold transportRecordedProperty
    apply congrArg ψI
    apply ProbabilityMeasure.toMeasure_injective
    change
      μ.toMeasure.map (recordedDecode (X := X) (A := A)) =
        (μ.toMeasure.map
          (worldActionRecordRelevanceMap (A := A) spec).pathMap).map
            (decodeRelevantPath (X := X) (A := A))
    rw [Measure.map_map
      decodeRelevantPath_measurable
      (worldActionRecordRelevanceMap (A := A) spec).pathMap_measurable]
    apply Measure.map_congr
    filter_upwards [] with w
    exact recordedDecode_factor_relevancePath spec w

/-- Confirmatory grounded Paper-I PR for action-sensitive decoded properties. -/
def IsPaperIRecordedGroundedPermanssonRegimeRelative
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : Prop :=
  M.IsPaperIConfirmatoryEGR spec m ∧
    M.IsPaperIRecordedConstitutive spec ψI J B₁

theorem paperIRecordedGroundedPermansson_iff_embeddedGroundedConfirmatoryPR
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    M.IsPaperIRecordedGroundedPermanssonRegimeRelative
        spec m ψI J B₁ ↔
      RegimeSpecification.IsGroundedConfirmatoryPermanssonRegimeRelative
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        (embeddedReferenceMeasure (A := A) m)
        (PaperIPolicyIntervention.transportedFamily M)
        (M.transportRecordedProperty ψI)
        (worldActionRecordRelevanceMap (A := A) spec)
        (PaperIComparisonSet.embedded M spec B₁)
        (J.transportedIntervention M) := by
  constructor
  · intro h
    refine ⟨
      (M.paperIConfirmatoryEGR_iff_embeddedConfirmatoryGR spec m).1 h.1,
      (M.paperIRecordedConstitutive_iff_embedded spec ψI J B₁).1 h.2,
      ?_⟩
    exact RegimeSpecification.GloballyFactorsThroughRelevanceMap.relative
      M.embeddedModel
      (embeddedSpec (A := A) spec)
      (PaperIPolicyIntervention.transportedFamily M)
      (M.transportRecordedProperty ψI)
      (worldActionRecordRelevanceMap (A := A) spec)
      (J.transportedIntervention M)
      (M.transportRecordedProperty_globallyGrounded spec ψI)
  · intro h
    exact ⟨
      (M.paperIConfirmatoryEGR_iff_embeddedConfirmatoryGR spec m).2 h.1,
      (M.paperIRecordedConstitutive_iff_embedded spec ψI J B₁).2 h.2.1⟩

section Metric

variable [MetricSpace Z]

def IsPaperIRecordedGroundedUniformPermanssonRegimeRelative
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : Prop :=
  M.IsPaperIConfirmatoryEGR spec m ∧
    M.IsPaperIRecordedUniformlyConstitutive spec ψI J B₁

theorem paperIRecordedGroundedUniformPermansson_iff_embeddedGroundedUniformPR
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : PaperIRecordedPropertyMap X A Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    M.IsPaperIRecordedGroundedUniformPermanssonRegimeRelative
        spec m ψI J B₁ ↔
      RegimeSpecification.IsGroundedConfirmatoryUniformPermanssonRegimeRelative
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        (embeddedReferenceMeasure (A := A) m)
        (PaperIPolicyIntervention.transportedFamily M)
        (M.transportRecordedProperty ψI)
        (worldActionRecordRelevanceMap (A := A) spec)
        (PaperIComparisonSet.embedded M spec B₁)
        (J.transportedIntervention M) := by
  constructor
  · intro h
    refine ⟨
      (M.paperIConfirmatoryEGR_iff_embeddedConfirmatoryGR spec m).1 h.1,
      (M.paperIRecordedUniformlyConstitutive_iff_embedded spec ψI J B₁).1 h.2,
      ?_⟩
    exact RegimeSpecification.GloballyFactorsThroughRelevanceMap.relative
      M.embeddedModel
      (embeddedSpec (A := A) spec)
      (PaperIPolicyIntervention.transportedFamily M)
      (M.transportRecordedProperty ψI)
      (worldActionRecordRelevanceMap (A := A) spec)
      (J.transportedIntervention M)
      (M.transportRecordedProperty_globallyGrounded spec ψI)
  · intro h
    exact ⟨
      (M.paperIConfirmatoryEGR_iff_embeddedConfirmatoryGR spec m).2 h.1,
      (M.paperIRecordedUniformlyConstitutive_iff_embedded spec ψI J B₁).2 h.2.1⟩

end Metric

end PaperISelectedModel

end PermanssonLean
