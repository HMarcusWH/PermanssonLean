import PermanssonLean.EGR.Specification
import PermanssonLean.Regime.Assumption41

open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace PermanssonLean

universe uX uA uH

namespace PaperISelectedModel

variable {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace H]
variable [TopologicalSpace X] [TopologicalSpace A]
variable [MeasurableSingletonClass A]
variable [MeasurableSpace.SeparatesPoints
  (JointState (PaperIStrategicState A) X)]

/-- Exact invariance is preserved by the canonical recording embedding. -/
theorem paperI_exactInvariant_iff_embedded
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H) :
    M.IsExactlyInvariant spec ↔
      RegimeSpecification.IsExactlyInvariant
        M.embeddedModel (embeddedSpec (A := A) spec) := by
  constructor
  · intro h y hy
    have hx : y.2 ∈ spec.region := hy.2
    let Q := recordingCompression (X := X) (A := A)
    let C : Set (JointState Unit X) :=
      unitWorldProjection ⁻¹' spec.region
    have hC : MeasurableSet C :=
      spec.region_measurable.preimage measurable_snd
    have hinter := kernelIntertwines_apply_preimage
      Q M.embeddedModel.inducedKernel M.unitModel.inducedKernel
      M.embedded_unit_kernelIntertwines y C hC
    have hset :
        Q.stateMap ⁻¹' C =
          (embeddedSpec (A := A) spec).region := by
      ext z
      simp [Q, C, embeddedSpec, recordingCompression,
        TypeRespectingStateCompression.stateMap,
        unitWorldProjection]
    rw [hset] at hinter
    have hunit :=
      M.unitModel_induced_apply y.2 spec.region_measurable
    have hbase := h y.2 hx
    have hchain := hinter.trans (hunit.trans hbase)
    simpa [Q, C, recordingCompression,
      TypeRespectingStateCompression.stateMap,
      unitWorldProjection] using hchain
  · intro h x hx
    let y : JointState (PaperIStrategicState A) X :=
      (initialStrategicState (A := A), x)
    have hy :
        y ∈ (embeddedSpec (A := A) spec).region := by
      exact ⟨Set.mem_univ _, hx⟩
    have hemb := h y hy
    let Q := recordingCompression (X := X) (A := A)
    let C : Set (JointState Unit X) :=
      unitWorldProjection ⁻¹' spec.region
    have hC : MeasurableSet C :=
      spec.region_measurable.preimage measurable_snd
    have hinter := kernelIntertwines_apply_preimage
      Q M.embeddedModel.inducedKernel M.unitModel.inducedKernel
      M.embedded_unit_kernelIntertwines y C hC
    have hset :
        Q.stateMap ⁻¹' C =
          (embeddedSpec (A := A) spec).region := by
      ext z
      simp [Q, C, embeddedSpec, recordingCompression,
        TypeRespectingStateCompression.stateMap,
        unitWorldProjection]
    rw [hset] at hinter
    have hunit :=
      M.unitModel_induced_apply x spec.region_measurable
    have hEq :
        M.equilibriumKernel x spec.region =
          M.embeddedModel.inducedKernel y
            (embeddedSpec (A := A) spec).region := by
      have hchain := (hinter.trans hunit).symm
      simpa [Q, C, y, recordingCompression,
        TypeRespectingStateCompression.stateMap,
        unitWorldProjection] using hchain
    exact hEq.trans hemb

/-- The transported convergence semantics on the enlarged model are exactly
the Paper-I convergence semantics of the enlarged law's world marginal. -/
theorem paperI_limiting_iff_embedded_worldMarginal
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (μ : ProbabilityMeasure
      (JointState (PaperIStrategicState A) X)) :
    RegimeSpecification.IsLimitingOccupationLaw
        M.embeddedModel (embeddedSpec (A := A) spec) μ ↔
      M.IsLimitingOccupationLaw spec (worldMarginal (A := A) μ) := by
  unfold RegimeSpecification.IsLimitingOccupationLaw
    IsLimitingOccupationLaw
  change
    spec.convergenceMode.holds
        ((M.embeddedModel.pathLaw μ.toMeasure).map
          (worldPathProjection
            (X := X) (S := PaperIStrategicState A)))
        (empiricalOccupation spec) spec.target ↔
      spec.convergenceMode.holds
        (M.pathLaw (worldMarginal (A := A) μ).toMeasure)
        (empiricalOccupation spec) spec.target
  rw [M.embedded_worldPathLaw_eq_paperI μ]

/-- Paper-I ex-ante nontriviality transports exactly to Assumption 4.1 on
the canonical recording representation when the lifted reference measure is
used. -/
theorem paperI_nontriviality_iff_embedded_assumption41
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X) :
    PaperINontriviality M spec m ↔
      RegimeSpecification.Assumption41
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        (embeddedReferenceMeasure (A := A) m) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases h.basin_nonempty with ⟨x, hx⟩
      exact ⟨(initialStrategicState (A := A), x), ⟨rfl, hx⟩⟩
    · rcases h.region_nontrivial with hinterior | hmass
      · left
        rcases hinterior with ⟨x, hx⟩
        rw [embeddedSpec, interior_prod_eq]
        exact ⟨(initialStrategicState (A := A), x),
          ⟨by simp, hx⟩⟩
      · right
        rw [embeddedReferenceMeasure_region
          (A := A) spec m]
        exact hmass
    · rcases h.descriptor_two_values with
        ⟨x₁, hx₁, x₂, hx₂, hne⟩
      refine ⟨(initialStrategicState (A := A), x₁),
        ⟨Set.mem_univ _, hx₁⟩,
        (initialStrategicState (A := A), x₂),
        ⟨Set.mem_univ _, hx₂⟩, ?_⟩
      simpa [embeddedSpec] using hne
    · rcases h.basin_two_states with
        ⟨x₁, hx₁, x₂, hx₂, hne⟩
      have htwo :
          RegimeSpecification.BasinHasTwoStates
            (embeddedSpec (A := A) spec) := by
        refine ⟨(initialStrategicState (A := A), x₁),
          ⟨rfl, hx₁⟩,
          (initialStrategicState (A := A), x₂),
          ⟨rfl, hx₂⟩, ?_⟩
        intro hpair
        exact hne (congrArg Prod.snd hpair)
      exact RegimeSpecification.two_states_implies_basinPathLawNontrivial
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        htwo
  · intro h
    refine {
      basin_nonempty := ?_
      region_nontrivial := ?_
      descriptor_two_values := ?_
      basin_two_states := ?_
    }
    · rcases h.1 with ⟨y, hy⟩
      exact ⟨y.2, hy.2⟩
    · rcases h.2.1 with hinterior | hmass
      · left
        rw [embeddedSpec, interior_prod_eq] at hinterior
        rcases hinterior with ⟨⟨s, x⟩, hs, hx⟩
        exact ⟨x, hx⟩
      · right
        rw [embeddedReferenceMeasure_region
          (A := A) spec m] at hmass
        exact hmass
    · rcases h.2.2.1 with
        ⟨y₁, hy₁, y₂, hy₂, hne⟩
      refine ⟨y₁.2, hy₁.2, y₂.2, hy₂.2, ?_⟩
      simpa [embeddedSpec] using hne
    · have htwo :=
        RegimeSpecification.assumption41_basin_has_two_states
          M.embeddedModel
          (embeddedSpec (A := A) spec)
          (embeddedReferenceMeasure (A := A) m)
          h
      rcases htwo with ⟨y₁, hy₁, y₂, hy₂, hne⟩
      refine ⟨y₁.2, hy₁.2, y₂.2, hy₂.2, ?_⟩
      intro hx
      apply hne
      apply Prod.ext
      · have hs₁ :
            y₁.1 = initialStrategicState (A := A) :=
          Set.mem_singleton_iff.mp hy₁.1
        have hs₂ :
            y₂.1 = initialStrategicState (A := A) :=
          Set.mem_singleton_iff.mp hy₂.1
        exact hs₁.trans hs₂.symm
      · exact hx

/-- Theorem 6.1, semantic core: the selected Paper-I object is an EGR iff
its canonical clock/action-recording embedding is an Exact GR. -/
theorem paperIEGR_iff_embeddedExactGR
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X) :
    IsPaperIEGR M spec m ↔
      RegimeSpecification.IsExactGeneratedRegime
        M.embeddedModel
        (embeddedSpec (A := A) spec)
        (embeddedReferenceMeasure (A := A) m) := by
  constructor
  · intro h
    refine ⟨RegimeSpecification.canonicalProcessWellPosed M.embeddedModel,
      ?_, ?_, ?_⟩
    · exact
        (paperI_nontriviality_iff_embedded_assumption41
          M spec m).1 h.1
    · exact
        (paperI_exactInvariant_iff_embedded M spec).1 h.2.1
    · intro μ hμ
      have hwm :
          IsAdmissibleInitialLaw spec (worldMarginal (A := A) μ) :=
        worldMarginal_admissible_of_embedded
          (A := A) spec μ hμ
      have hlim := h.2.2 (worldMarginal (A := A) μ) hwm
      exact
        (paperI_limiting_iff_embedded_worldMarginal
          M spec μ).2 hlim
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact
        (paperI_nontriviality_iff_embedded_assumption41
          M spec m).2 h.2.1
    · exact
        (paperI_exactInvariant_iff_embedded M spec).2 h.2.2.1
    · intro μ hμ
      have hembAdm :
          IsAdmissibleInitialLaw
            (embeddedSpec (A := A) spec)
            (embeddedInitialLaw (A := A) μ) :=
        (embeddedInitialLaw_admissible_iff
          (A := A) spec μ).2 hμ
      have hembLim :=
        h.2.2.2 (embeddedInitialLaw (A := A) μ) hembAdm
      have hpaper :=
        (paperI_limiting_iff_embedded_worldMarginal
          M spec (embeddedInitialLaw (A := A) μ)).1 hembLim
      simpa using hpaper

end PaperISelectedModel

end PermanssonLean
