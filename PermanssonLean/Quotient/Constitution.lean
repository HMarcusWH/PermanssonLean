import PermanssonLean.Quotient.RegimeSemantics
import PermanssonLean.Regime.ConstitutiveMargin
import PermanssonLean.Regime.FamilyEquivalence
import Mathlib.MeasureTheory.Measure.DiracProba

open MeasureTheory ProbabilityTheory Set

namespace PermanssonLean

universe uS uX uA uSbar uXbar uAbar uH uZ uK₁ uK₂ uL₁ uL₂

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {Sbar : Type uSbar} {Xbar : Type uXbar} {Abar : Type uAbar}
variable {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace Sbar] [MeasurableSpace Xbar] [MeasurableSpace Abar]
variable [MeasurableSpace H]

/-- The frozen property map factors through path compression. -/
def PropertyFactorsThroughCompression
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (ψbar : RegimePropertyMap (JointState Sbar Xbar) Z) : Prop :=
  ∀ μ : ProbabilityMeasure (ℕ → JointState S X),
    ψ μ = ψbar (Q.pushPath μ)

/-- The two independently certified comparison sets represent the same
declared comparison region through q. -/
structure QuotientCompatibleComparisonSets
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    {M : StrategicWorldModel S X A}
    {Mbar : StrategicWorldModel Sbar Xbar Abar}
    {spec : RegimeSpecification (JointState S X) H}
    {specbar : RegimeSpecification (JointState Sbar Xbar) H}
    (B₁ : RegimeSpecification.ConstitutiveComparisonSet M spec)
    (Bbar₁ : RegimeSpecification.ConstitutiveComparisonSet Mbar specbar) where
  states_preimage :
    B₁.states = Q.stateMap ⁻¹' Bbar₁.states

namespace TypeRespectingStateCompression

theorem pushInitial_dirac
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (y : JointState S X) :
    Q.pushInitial (diracProba y) = diracProba (Q.stateMap y) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.dirac y).map Q.stateMap =
    Measure.dirac (Q.stateMap y)
  exact Measure.map_dirac' Q.stateMap_measurable y

end TypeRespectingStateCompression

namespace QuotientCompatibleComparisonSets

theorem comparison_surjective
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    {M : StrategicWorldModel S X A}
    {Mbar : StrategicWorldModel Sbar Xbar Abar}
    {spec : RegimeSpecification (JointState S X) H}
    {specbar : RegimeSpecification (JointState Sbar Xbar) H}
    {B₁ : RegimeSpecification.ConstitutiveComparisonSet M spec}
    {Bbar₁ : RegimeSpecification.ConstitutiveComparisonSet Mbar specbar}
    (C : QuotientCompatibleComparisonSets Q B₁ Bbar₁) :
    Set.SurjOn Q.stateMap B₁.states Bbar₁.states := by
  intro ybar hybar
  rcases Q.stateMap_surjective ybar with ⟨y, hy⟩
  refine ⟨y, ?_, hy⟩
  rw [C.states_preimage]
  simpa [hy] using hybar

end QuotientCompatibleComparisonSets

namespace RegimeSpecification

theorem baselinePropertyValue_eq_under_quotient
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    (M : StrategicWorldModel S X A)
    (Mbar : StrategicWorldModel Sbar Xbar Abar)
    (hK : KernelIntertwines Q M.inducedKernel Mbar.inducedKernel)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (ψbar : RegimePropertyMap (JointState Sbar Xbar) Z)
    (hψ : PropertyFactorsThroughCompression Q ψ ψbar)
    (y : JointState S X) :
    baselinePropertyValue ψ M y =
      baselinePropertyValue ψbar Mbar (Q.stateMap y) := by
  unfold baselinePropertyValue
  rw [hψ]
  rw [pathProbability_push_eq_of_kernelIntertwines
    Q M Mbar hK (diracProba y)]
  rw [Q.pushInitial_dirac y]

theorem intervenedPropertyValue_eq_under_quotient
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    {M : StrategicWorldModel S X A}
    {Mbar : StrategicWorldModel Sbar Xbar Abar}
    {Component : Type uK₁} {ComponentBar : Type uK₂}
    {Label : Type uL₁} {LabelBar : Type uL₂}
    (F : InterventionFamily M Component)
    (Fbar : InterventionFamily Mbar ComponentBar)
    (J : FrozenStrategicInterventionFamily F Label)
    (Jbar : FrozenStrategicInterventionFamily Fbar LabelBar)
    (KQ : InterventionCompatibleKernelQuotient Q F Fbar J Jbar)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (ψbar : RegimePropertyMap (JointState Sbar Xbar) Z)
    (hψ : PropertyFactorsThroughCompression Q ψ ψbar)
    (l : Label)
    (y : JointState S X) :
    intervenedPropertyValue ψ (J.intervention l).intervention y =
      intervenedPropertyValue ψbar
        (Jbar.intervention (KQ.matching.labelEquiv l)).intervention
        (Q.stateMap y) := by
  unfold intervenedPropertyValue
  rw [hψ]
  rw [pathProbability_push_eq_of_kernelIntertwines
    Q
    (J.intervention l).intervention.apply
    (Jbar.intervention (KQ.matching.labelEquiv l)).intervention.apply
    (KQ.intervention_intertwines l)
    (diracProba y)]
  rw [Q.pushInitial_dirac y]

theorem strategicallyConstitutive_iff_under_quotient
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    {M : StrategicWorldModel S X A}
    {Mbar : StrategicWorldModel Sbar Xbar Abar}
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H)
    {Component : Type uK₁} {ComponentBar : Type uK₂}
    {Label : Type uL₁} {LabelBar : Type uL₂}
    (F : InterventionFamily M Component)
    (Fbar : InterventionFamily Mbar ComponentBar)
    (J : FrozenStrategicInterventionFamily F Label)
    (Jbar : FrozenStrategicInterventionFamily Fbar LabelBar)
    (KQ : InterventionCompatibleKernelQuotient Q F Fbar J Jbar)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (ψbar : RegimePropertyMap (JointState Sbar Xbar) Z)
    (hψ : PropertyFactorsThroughCompression Q ψ ψbar)
    (B₁ : ConstitutiveComparisonSet M spec)
    (Bbar₁ : ConstitutiveComparisonSet Mbar specbar)
    (CB : QuotientCompatibleComparisonSets Q B₁ Bbar₁)
    (l : Label) :
    IsStrategicallyConstitutive M spec F ψ B₁ (J.intervention l) ↔
      IsStrategicallyConstitutive Mbar specbar Fbar ψbar Bbar₁
        (Jbar.intervention (KQ.matching.labelEquiv l)) := by
  constructor
  · intro h ybar hybar
    rcases QuotientCompatibleComparisonSets.comparison_surjective Q CB hybar with ⟨y, hy, hqy⟩
    have hbase := baselinePropertyValue_eq_under_quotient
      Q M Mbar KQ.baseline_intertwines ψ ψbar hψ y
    have hinter := intervenedPropertyValue_eq_under_quotient
      Q F Fbar J Jbar KQ ψ ψbar hψ l y
    simpa [hqy, hbase, hinter] using h y hy
  · intro h y hy
    have hybar : Q.stateMap y ∈ Bbar₁.states := by
      rw [CB.states_preimage] at hy
      exact hy
    have hbase := baselinePropertyValue_eq_under_quotient
      Q M Mbar KQ.baseline_intertwines ψ ψbar hψ y
    have hinter := intervenedPropertyValue_eq_under_quotient
      Q F Fbar J Jbar KQ ψ ψbar hψ l y
    simpa [hbase, hinter] using h (Q.stateMap y) hybar

section Metric

variable [MetricSpace Z]

theorem constitutiveEffect_eq_under_quotient
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    {M : StrategicWorldModel S X A}
    {Mbar : StrategicWorldModel Sbar Xbar Abar}
    {Component : Type uK₁} {ComponentBar : Type uK₂}
    {Label : Type uL₁} {LabelBar : Type uL₂}
    (F : InterventionFamily M Component)
    (Fbar : InterventionFamily Mbar ComponentBar)
    (J : FrozenStrategicInterventionFamily F Label)
    (Jbar : FrozenStrategicInterventionFamily Fbar LabelBar)
    (KQ : InterventionCompatibleKernelQuotient Q F Fbar J Jbar)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (ψbar : RegimePropertyMap (JointState Sbar Xbar) Z)
    (hψ : PropertyFactorsThroughCompression Q ψ ψbar)
    (l : Label)
    (y : JointState S X) :
    constitutiveEffect M ψ (J.intervention l) y =
      constitutiveEffect Mbar ψbar
        (Jbar.intervention (KQ.matching.labelEquiv l))
        (Q.stateMap y) := by
  unfold constitutiveEffect
  rw [
    baselinePropertyValue_eq_under_quotient
      Q M Mbar KQ.baseline_intertwines ψ ψbar hψ y,
    intervenedPropertyValue_eq_under_quotient
      Q F Fbar J Jbar KQ ψ ψbar hψ l y
  ]

theorem constitutiveMargin_eq_under_quotient
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    {M : StrategicWorldModel S X A}
    {Mbar : StrategicWorldModel Sbar Xbar Abar}
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H)
    {Component : Type uK₁} {ComponentBar : Type uK₂}
    {Label : Type uL₁} {LabelBar : Type uL₂}
    (F : InterventionFamily M Component)
    (Fbar : InterventionFamily Mbar ComponentBar)
    (J : FrozenStrategicInterventionFamily F Label)
    (Jbar : FrozenStrategicInterventionFamily Fbar LabelBar)
    (KQ : InterventionCompatibleKernelQuotient Q F Fbar J Jbar)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (ψbar : RegimePropertyMap (JointState Sbar Xbar) Z)
    (hψ : PropertyFactorsThroughCompression Q ψ ψbar)
    (B₁ : ConstitutiveComparisonSet M spec)
    (Bbar₁ : ConstitutiveComparisonSet Mbar specbar)
    (CB : QuotientCompatibleComparisonSets Q B₁ Bbar₁)
    (l : Label) :
    constitutiveMargin M spec F ψ B₁ (J.intervention l) =
      constitutiveMargin Mbar specbar Fbar ψbar Bbar₁
        (Jbar.intervention (KQ.matching.labelEquiv l)) := by
  unfold constitutiveMargin
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Q.stateMap y, ?_, ?_⟩
    · rw [CB.states_preimage] at hy
      exact hy
    · exact (constitutiveEffect_eq_under_quotient
        Q F Fbar J Jbar KQ ψ ψbar hψ l y).symm
  · rintro ⟨ybar, hybar, hr⟩
    rcases QuotientCompatibleComparisonSets.comparison_surjective Q CB hybar with ⟨y, hy, hqy⟩
    refine ⟨y, hy, ?_⟩
    rw [constitutiveEffect_eq_under_quotient
      Q F Fbar J Jbar KQ ψ ψbar hψ l y, hqy]
    exact hr

theorem uniformlyConstitutive_iff_under_quotient
    (Q : TypeRespectingStateCompression S X Sbar Xbar)
    {M : StrategicWorldModel S X A}
    {Mbar : StrategicWorldModel Sbar Xbar Abar}
    (spec : RegimeSpecification (JointState S X) H)
    (specbar : RegimeSpecification (JointState Sbar Xbar) H)
    {Component : Type uK₁} {ComponentBar : Type uK₂}
    {Label : Type uL₁} {LabelBar : Type uL₂}
    (F : InterventionFamily M Component)
    (Fbar : InterventionFamily Mbar ComponentBar)
    (J : FrozenStrategicInterventionFamily F Label)
    (Jbar : FrozenStrategicInterventionFamily Fbar LabelBar)
    (KQ : InterventionCompatibleKernelQuotient Q F Fbar J Jbar)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (ψbar : RegimePropertyMap (JointState Sbar Xbar) Z)
    (hψ : PropertyFactorsThroughCompression Q ψ ψbar)
    (B₁ : ConstitutiveComparisonSet M spec)
    (Bbar₁ : ConstitutiveComparisonSet Mbar specbar)
    (CB : QuotientCompatibleComparisonSets Q B₁ Bbar₁)
    (l : Label) :
    IsUniformlyStrategicallyConstitutive M spec F ψ B₁ (J.intervention l) ↔
      IsUniformlyStrategicallyConstitutive Mbar specbar Fbar ψbar Bbar₁
        (Jbar.intervention (KQ.matching.labelEquiv l)) := by
  rw [
    uniformlyConstitutive_iff_margin_pos,
    uniformlyConstitutive_iff_margin_pos,
    constitutiveMargin_eq_under_quotient
      Q spec specbar F Fbar J Jbar KQ ψ ψbar hψ B₁ Bbar₁ CB l
  ]

end Metric

end RegimeSpecification

end PermanssonLean
