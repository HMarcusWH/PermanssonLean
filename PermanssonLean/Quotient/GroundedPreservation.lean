import PermanssonLean.Regime.GroundedFamilyEquivalence
import PermanssonLean.Quotient.Preservation

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uSbar uXbar uAbar uH uG uZ uK₁ uK₂ uL₁ uL₂

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {Sbar : Type uSbar} {Xbar : Type uXbar} {Abar : Type uAbar}
variable {H : Type uH} {G : Type uG} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace Sbar] [MeasurableSpace Xbar] [MeasurableSpace Abar]
variable [MeasurableSpace H] [MeasurableSpace G]
variable [TopologicalSpace S] [TopologicalSpace X]
variable [TopologicalSpace Sbar] [TopologicalSpace Xbar]

/-- Grounded observation commutes with the type-respecting state compression:
g = gbar ∘ q. -/
structure RelevanceMapFactorsThroughCompression
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    {spec : RegimeSpecification (JointState S X) H}
    {specbar : RegimeSpecification (JointState Sbar Xbar) H}
    (g : RegimeSpecification.GroundedRelevanceMap spec G)
    (gbar : RegimeSpecification.GroundedRelevanceMap specbar G) : Prop where
  observe_factor :
    g.observe = gbar.observe ∘ Q.stateMap

namespace RelevanceMapFactorsThroughCompression

theorem pathMap_factor
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    {spec : RegimeSpecification (JointState S X) H}
    {specbar : RegimeSpecification (JointState Sbar Xbar) H}
    (g : RegimeSpecification.GroundedRelevanceMap spec G)
    (gbar : RegimeSpecification.GroundedRelevanceMap specbar G)
    (C : RelevanceMapFactorsThroughCompression Q g gbar)
    (w : ℕ → JointState S X) :
    g.pathMap w = gbar.pathMap (Q.pathMap w) := by
  funext n
  have h := congrFun C.observe_factor (w n)
  simpa [
    RegimeSpecification.GroundedRelevanceMap.pathMap,
    TypeRespectingStateCompression.pathMap,
    Function.comp_def
  ] using h

theorem pushPath_eq
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    {spec : RegimeSpecification (JointState S X) H}
    {specbar : RegimeSpecification (JointState Sbar Xbar) H}
    (g : RegimeSpecification.GroundedRelevanceMap spec G)
    (gbar : RegimeSpecification.GroundedRelevanceMap specbar G)
    (C : RelevanceMapFactorsThroughCompression Q g gbar)
    (μ : ProbabilityMeasure (ℕ → JointState S X)) :
    g.pushPath μ = gbar.pushPath (Q.pushPath μ) := by
  apply ProbabilityMeasure.toMeasure_injective
  change μ.toMeasure.map g.pathMap =
    (μ.toMeasure.map Q.pathMap).map gbar.pathMap
  rw [Measure.map_map gbar.pathMap_measurable Q.pathMap_measurable]
  apply Measure.map_congr
  filter_upwards [] with w
  exact C.pathMap_factor Q g gbar w

end RelevanceMapFactorsThroughCompression

namespace RegimeSpecification

theorem descriptorLaw_push_eq_under_quotient
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sbar Xbar Abar)
    (hK : KernelIntertwines Q M.inducedKernel Mbar.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H)
    (C : QuotientCompatibleRegimeSpecifications Q spec specbar)
    (μ : ProbabilityMeasure (JointState S X))
    (t : ℕ) :
    descriptorLaw M spec μ t =
      descriptorLaw Mbar specbar (Q.pushInitial μ) t := by
  unfold descriptorLaw
  have hpath :=
    pathProbability_push_eq_of_kernelIntertwines Q M Mbar hK μ
  rw [← hpath]
  apply ProbabilityMeasure.toMeasure_injective
  change
    (pathProbability M μ).toMeasure.map
        (fun w => spec.descriptor (w t)) =
      ((pathProbability M μ).toMeasure.map Q.pathMap).map
        (fun w => specbar.descriptor (w t))
  rw [Measure.map_map
    (measurable_descriptorAt specbar t)
    Q.pathMap_measurable]
  apply Measure.map_congr
  filter_upwards [] with w
  have hf := congrFun C.descriptor_factor (w t)
  simpa [TypeRespectingStateCompression.pathMap, Function.comp_def] using hf

theorem descriptorNondegenerate_iff_under_quotient
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sbar Xbar Abar)
    (hK : KernelIntertwines Q M.inducedKernel Mbar.inducedKernel)
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H)
    (C : QuotientCompatibleRegimeSpecifications Q spec specbar) :
    IsDescriptorNondegenerate M spec ↔
      IsDescriptorNondegenerate Mbar specbar := by
  constructor
  · rintro ⟨y₁, hy₁, t₁, y₂, hy₂, t₂, hne⟩
    refine ⟨Q.stateMap y₁, ?_, t₁, Q.stateMap y₂, ?_, t₂, ?_⟩
    · rw [C.basin_preimage] at hy₁
      exact hy₁
    · rw [C.basin_preimage] at hy₂
      exact hy₂
    · have h₁ := descriptorLaw_push_eq_under_quotient
        Q M Mbar hK spec specbar C (diracProba y₁) t₁
      have h₂ := descriptorLaw_push_eq_under_quotient
        Q M Mbar hK spec specbar C (diracProba y₂) t₂
      rw [Q.pushInitial_dirac y₁] at h₁
      rw [Q.pushInitial_dirac y₂] at h₂
      intro heq
      exact hne (h₁.trans (heq.trans h₂.symm))
  · rintro ⟨ybar₁, hybar₁, t₁, ybar₂, hybar₂, t₂, hne⟩
    rcases Q.stateMap_surjective ybar₁ with ⟨y₁, hy₁q⟩
    rcases Q.stateMap_surjective ybar₂ with ⟨y₂, hy₂q⟩
    have hy₁ : y₁ ∈ spec.basin := by
      rw [C.basin_preimage]
      simpa [hy₁q] using hybar₁
    have hy₂ : y₂ ∈ spec.basin := by
      rw [C.basin_preimage]
      simpa [hy₂q] using hybar₂
    refine ⟨y₁, hy₁, t₁, y₂, hy₂, t₂, ?_⟩
    have h₁ := descriptorLaw_push_eq_under_quotient
      Q M Mbar hK spec specbar C (diracProba y₁) t₁
    have h₂ := descriptorLaw_push_eq_under_quotient
      Q M Mbar hK spec specbar C (diracProba y₂) t₂
    rw [Q.pushInitial_dirac y₁, hy₁q] at h₁
    rw [Q.pushInitial_dirac y₂, hy₂q] at h₂
    intro heq
    exact hne (h₁.symm.trans (heq.trans h₂))

theorem quotient_confirmatoryGR_iff
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sbar Xbar Abar)
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H)
    (m : Measure (JointState S X))
    (mbar : Measure (JointState Sbar Xbar))
    {Component : Type uK₁} {ComponentBar : Type uK₂}
    {Label : Type uL₁} {LabelBar : Type uL₂}
    (F : InterventionFamily M Component)
    (Fbar : InterventionFamily Mbar ComponentBar)
    (J : FrozenStrategicInterventionFamily F Label)
    (Jbar : FrozenStrategicInterventionFamily Fbar LabelBar)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (ψbar : RegimePropertyMap (JointState Sbar Xbar) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (Bbar₁ : ConstitutiveComparisonSet Mbar specbar)
    (C : InterventionCompatibleStateQuotient
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar B₁ Bbar₁) :
    IsConfirmatoryGeneratedRegime M spec m ↔
      IsConfirmatoryGeneratedRegime Mbar specbar mbar := by
  unfold IsConfirmatoryGeneratedRegime
  rw [
    quotient_exactGR_iff
      Q M Mbar spec specbar m mbar
      F Fbar J Jbar ψ ψbar B₁ Bbar₁ C,
    descriptorNondegenerate_iff_under_quotient
      Q M Mbar C.kernel.baseline_intertwines
      spec specbar C.regime
  ]

theorem groundedFrozenFamilyProperty_iff_under_quotient
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sbar Xbar Abar)
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H)
    (m : Measure (JointState S X))
    (mbar : Measure (JointState Sbar Xbar))
    {Component : Type uK₁} {ComponentBar : Type uK₂}
    {Label : Type uL₁} {LabelBar : Type uL₂}
    (F : InterventionFamily M Component)
    (Fbar : InterventionFamily Mbar ComponentBar)
    (J : FrozenStrategicInterventionFamily F Label)
    (Jbar : FrozenStrategicInterventionFamily Fbar LabelBar)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (ψbar : RegimePropertyMap (JointState Sbar Xbar) Z)
    (g : GroundedRelevanceMap spec G)
    (gbar : GroundedRelevanceMap specbar G)
    (Rg : RelevanceMapFactorsThroughCompression Q g gbar)
    (B₁ : ConstitutiveComparisonSet M spec)
    (Bbar₁ : ConstitutiveComparisonSet Mbar specbar)
    (C : InterventionCompatibleStateQuotient
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar B₁ Bbar₁) :
    GroundedFrozenFamilyProperty M spec F J ψ g ↔
      GroundedFrozenFamilyProperty Mbar specbar Fbar Jbar ψbar gbar := by
  let φ := C.kernel.matching.labelEquiv
  constructor
  · rintro ⟨ψG, hbase, hinter⟩
    refine ⟨ψG, ?_, ?_⟩
    · intro μbar hμbar
      rcases C.admissible_lifts μbar hμbar with ⟨μ, hμ, hpush⟩
      have hpath :=
        pathProbability_push_eq_of_kernelIntertwines
          Q M Mbar C.kernel.baseline_intertwines μ
      have hψ := C.property (pathProbability M μ)
      have hgpush := Rg.pushPath_eq Q g gbar (pathProbability M μ)
      have hground := hbase μ hμ
      rw [hpush] at hpath
      rw [← hpath]
      exact hψ.symm.trans (hground.trans (congrArg ψG hgpush))
    · intro lbar μbar hμbar
      let l : Label := φ.symm lbar
      rcases C.admissible_lifts μbar hμbar with ⟨μ, hμ, hpush⟩
      have hK :
          KernelIntertwines Q
            (J.intervention l).intervention.apply.inducedKernel
            (Jbar.intervention lbar).intervention.apply.inducedKernel := by
        simpa [l, φ] using C.kernel.intervention_intertwines l
      have hpath :=
        pathProbability_push_eq_of_kernelIntertwines Q
          (J.intervention l).intervention.apply
          (Jbar.intervention lbar).intervention.apply hK μ
      have hψ := C.property
        (pathProbability (J.intervention l).intervention.apply μ)
      have hgpush := Rg.pushPath_eq Q g gbar
        (pathProbability (J.intervention l).intervention.apply μ)
      have hground := hinter l μ hμ
      rw [hpush] at hpath
      rw [← hpath]
      exact hψ.symm.trans (hground.trans (congrArg ψG hgpush))
  · rintro ⟨ψG, hbase, hinter⟩
    refine ⟨ψG, ?_, ?_⟩
    · intro μ hμ
      have hμbar :=
        pushInitial_admissible Q spec specbar C.regime μ hμ
      have hpath :=
        pathProbability_push_eq_of_kernelIntertwines
          Q M Mbar C.kernel.baseline_intertwines μ
      have hψ := C.property (pathProbability M μ)
      have hgpush := Rg.pushPath_eq Q g gbar (pathProbability M μ)
      have hground := hbase (Q.pushInitial μ) hμbar
      rw [← hpath] at hground
      rw [← hgpush] at hground
      exact hψ.trans hground
    · intro l μ hμ
      have hμbar :=
        pushInitial_admissible Q spec specbar C.regime μ hμ
      have hK := C.kernel.intervention_intertwines l
      have hpath :=
        pathProbability_push_eq_of_kernelIntertwines Q
          (J.intervention l).intervention.apply
          (Jbar.intervention (φ l)).intervention.apply hK μ
      have hψ := C.property
        (pathProbability (J.intervention l).intervention.apply μ)
      have hgpush := Rg.pushPath_eq Q g gbar
        (pathProbability (J.intervention l).intervention.apply μ)
      have hground := hinter (φ l) (Q.pushInitial μ) hμbar
      rw [← hpath] at hground
      rw [← hgpush] at hground
      exact hψ.trans hground

theorem quotient_groundedFrozenFamilyPR_iff
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sbar Xbar Abar)
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H)
    (m : Measure (JointState S X))
    (mbar : Measure (JointState Sbar Xbar))
    {Component : Type uK₁} {ComponentBar : Type uK₂}
    {Label : Type uL₁} {LabelBar : Type uL₂}
    (F : InterventionFamily M Component)
    (Fbar : InterventionFamily Mbar ComponentBar)
    (J : FrozenStrategicInterventionFamily F Label)
    (Jbar : FrozenStrategicInterventionFamily Fbar LabelBar)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (ψbar : RegimePropertyMap (JointState Sbar Xbar) Z)
    (g : GroundedRelevanceMap spec G)
    (gbar : GroundedRelevanceMap specbar G)
    (Rg : RelevanceMapFactorsThroughCompression Q g gbar)
    (B₁ : ConstitutiveComparisonSet M spec)
    (Bbar₁ : ConstitutiveComparisonSet Mbar specbar)
    (C : InterventionCompatibleStateQuotient
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar B₁ Bbar₁) :
    IsGroundedFrozenFamilyPermanssonRegime M spec m F J ψ g B₁ ↔
      IsGroundedFrozenFamilyPermanssonRegime
        Mbar specbar mbar Fbar Jbar ψbar gbar Bbar₁ := by
  unfold IsGroundedFrozenFamilyPermanssonRegime
  rw [
    quotient_confirmatoryGR_iff
      Q M Mbar spec specbar m mbar
      F Fbar J Jbar ψ ψbar B₁ Bbar₁ C,
    groundedFrozenFamilyProperty_iff_under_quotient
      Q M Mbar spec specbar m mbar
      F Fbar J Jbar ψ ψbar g gbar Rg B₁ Bbar₁ C,
    quotient_hasConstitutiveWitness_iff
      Q M Mbar spec specbar m mbar
      F Fbar J Jbar ψ ψbar B₁ Bbar₁ C
  ]

section Metric

variable [MetricSpace Z]

theorem quotient_groundedFrozenFamilyUniformPR_iff
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sbar Xbar Abar)
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H)
    (m : Measure (JointState S X))
    (mbar : Measure (JointState Sbar Xbar))
    {Component : Type uK₁} {ComponentBar : Type uK₂}
    {Label : Type uL₁} {LabelBar : Type uL₂}
    (F : InterventionFamily M Component)
    (Fbar : InterventionFamily Mbar ComponentBar)
    (J : FrozenStrategicInterventionFamily F Label)
    (Jbar : FrozenStrategicInterventionFamily Fbar LabelBar)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (ψbar : RegimePropertyMap (JointState Sbar Xbar) Z)
    (g : GroundedRelevanceMap spec G)
    (gbar : GroundedRelevanceMap specbar G)
    (Rg : RelevanceMapFactorsThroughCompression Q g gbar)
    (B₁ : ConstitutiveComparisonSet M spec)
    (Bbar₁ : ConstitutiveComparisonSet Mbar specbar)
    (C : InterventionCompatibleStateQuotient
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar B₁ Bbar₁) :
    IsGroundedFrozenFamilyUniformPermanssonRegime
        M spec m F J ψ g B₁ ↔
      IsGroundedFrozenFamilyUniformPermanssonRegime
        Mbar specbar mbar Fbar Jbar ψbar gbar Bbar₁ := by
  unfold IsGroundedFrozenFamilyUniformPermanssonRegime
  rw [
    quotient_confirmatoryGR_iff
      Q M Mbar spec specbar m mbar
      F Fbar J Jbar ψ ψbar B₁ Bbar₁ C,
    groundedFrozenFamilyProperty_iff_under_quotient
      Q M Mbar spec specbar m mbar
      F Fbar J Jbar ψ ψbar g gbar Rg B₁ Bbar₁ C,
    quotient_hasUniformConstitutiveWitness_iff
      Q M Mbar spec specbar m mbar
      F Fbar J Jbar ψ ψbar B₁ Bbar₁ C
  ]

end Metric

end RegimeSpecification

end PermanssonLean
