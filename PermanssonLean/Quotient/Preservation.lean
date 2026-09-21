import PermanssonLean.Quotient.Constitution
import PermanssonLean.Regime.FamilyEquivalence

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uSbar uXbar uAbar uH uZ uK₁ uK₂ uL₁ uL₂

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {Sbar : Type uSbar} {Xbar : Type uXbar} {Abar : Type uAbar}
variable {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace Sbar] [MeasurableSpace Xbar] [MeasurableSpace Abar]
variable [MeasurableSpace H]
variable [TopologicalSpace S] [TopologicalSpace X]
variable [TopologicalSpace Sbar] [TopologicalSpace Xbar]

/-- Full semantic certificate for the general/uniform core of the
type-respecting intervention-compatible quotient theorem. -/
structure InterventionCompatibleStateQuotient
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
    (B₁ : RegimeSpecification.ConstitutiveComparisonSet M spec)
    (Bbar₁ : RegimeSpecification.ConstitutiveComparisonSet Mbar specbar) where
  kernel :
    InterventionCompatibleKernelQuotient Q F Fbar J Jbar
  regime :
    QuotientCompatibleRegimeSpecifications Q spec specbar
  comparison :
    QuotientCompatibleComparisonSets Q B₁ Bbar₁
  convergence :
    ConvergenceModesCompatibleUnderCompression Q spec specbar
  property :
    PropertyFactorsThroughCompression Q ψ ψbar
  admissible_lifts :
    HasAdmissibleInitialLifts Q spec specbar
  original_nontrivial :
    RegimeSpecification.Assumption41 M spec m
  quotient_nontrivial :
    RegimeSpecification.Assumption41 Mbar specbar mbar

namespace RegimeSpecification

theorem quotient_exactGR_iff
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
    IsExactGeneratedRegime M spec m ↔
      IsExactGeneratedRegime Mbar specbar mbar := by
  exact exactGR_iff_of_quotient
    Q M Mbar C.kernel.baseline_intertwines
    spec specbar C.regime C.convergence C.admissible_lifts
    m mbar C.original_nontrivial C.quotient_nontrivial

theorem quotient_constitutive_iff_each_label
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
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar B₁ Bbar₁)
    (l : Label) :
    IsStrategicallyConstitutive M spec F ψ B₁ (J.intervention l) ↔
      IsStrategicallyConstitutive Mbar specbar Fbar ψbar Bbar₁
        (Jbar.intervention (C.kernel.matching.labelEquiv l)) := by
  exact strategicallyConstitutive_iff_under_quotient
    Q spec specbar F Fbar J Jbar C.kernel ψ ψbar C.property
    B₁ Bbar₁ C.comparison l

theorem quotient_hasConstitutiveWitness_iff
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
    HasConstitutiveWitnessInFrozenFamily M spec F J ψ B₁ ↔
      HasConstitutiveWitnessInFrozenFamily Mbar specbar Fbar Jbar ψbar Bbar₁ := by
  let φ := C.kernel.matching.labelEquiv
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨φ l, ?_⟩
    exact (quotient_constitutive_iff_each_label
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar
      B₁ Bbar₁ C l).1 hl
  · rintro ⟨lbar, hlbar⟩
    let l : Label := φ.symm lbar
    refine ⟨l, ?_⟩
    have hiff := quotient_constitutive_iff_each_label
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar
      B₁ Bbar₁ C l
    simpa [l, φ] using hiff.mpr hlbar

/-- Theorem 7.4b, generalized-PR family form: Exact-GR status and existence
of a constitutive witness in the frozen family are jointly preserved. -/
theorem quotient_frozenFamilyPR_iff
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
    IsFrozenFamilyPermanssonRegime M spec m F J ψ B₁ ↔
      IsFrozenFamilyPermanssonRegime Mbar specbar mbar Fbar Jbar ψbar Bbar₁ := by
  unfold IsFrozenFamilyPermanssonRegime
  rw [
    quotient_exactGR_iff
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar B₁ Bbar₁ C,
    quotient_hasConstitutiveWitness_iff
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar B₁ Bbar₁ C
  ]

section Metric

variable [MetricSpace Z]

theorem quotient_effect_eq_each_label
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
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar B₁ Bbar₁)
    (l : Label)
    (y : JointState S X) :
    constitutiveEffect M ψ (J.intervention l) y =
      constitutiveEffect Mbar ψbar
        (Jbar.intervention (C.kernel.matching.labelEquiv l))
        (Q.stateMap y) := by
  exact constitutiveEffect_eq_under_quotient
    Q F Fbar J Jbar C.kernel ψ ψbar C.property l y

theorem quotient_margin_eq_each_label
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
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar B₁ Bbar₁)
    (l : Label) :
    constitutiveMargin M spec F ψ B₁ (J.intervention l) =
      constitutiveMargin Mbar specbar Fbar ψbar Bbar₁
        (Jbar.intervention (C.kernel.matching.labelEquiv l)) := by
  exact constitutiveMargin_eq_under_quotient
    Q spec specbar F Fbar J Jbar C.kernel ψ ψbar C.property
    B₁ Bbar₁ C.comparison l

theorem quotient_uniformConstitutive_iff_each_label
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
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar B₁ Bbar₁)
    (l : Label) :
    IsUniformlyStrategicallyConstitutive M spec F ψ B₁ (J.intervention l) ↔
      IsUniformlyStrategicallyConstitutive Mbar specbar Fbar ψbar Bbar₁
        (Jbar.intervention (C.kernel.matching.labelEquiv l)) := by
  exact uniformlyConstitutive_iff_under_quotient
    Q spec specbar F Fbar J Jbar C.kernel ψ ψbar C.property
    B₁ Bbar₁ C.comparison l

theorem quotient_hasUniformConstitutiveWitness_iff
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
    HasUniformConstitutiveWitnessInFrozenFamily M spec F J ψ B₁ ↔
      HasUniformConstitutiveWitnessInFrozenFamily
        Mbar specbar Fbar Jbar ψbar Bbar₁ := by
  let φ := C.kernel.matching.labelEquiv
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨φ l, ?_⟩
    exact (quotient_uniformConstitutive_iff_each_label
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar
      B₁ Bbar₁ C l).1 hl
  · rintro ⟨lbar, hlbar⟩
    let l : Label := φ.symm lbar
    refine ⟨l, ?_⟩
    have hiff := quotient_uniformConstitutive_iff_each_label
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar
      B₁ Bbar₁ C l
    simpa [l, φ] using hiff.mpr hlbar

/-- Uniform-margin family form of Theorem 7.4b. -/
theorem quotient_frozenFamilyUniformPR_iff
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
    IsFrozenFamilyUniformPermanssonRegime M spec m F J ψ B₁ ↔
      IsFrozenFamilyUniformPermanssonRegime
        Mbar specbar mbar Fbar Jbar ψbar Bbar₁ := by
  unfold IsFrozenFamilyUniformPermanssonRegime
  rw [
    quotient_exactGR_iff
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar B₁ Bbar₁ C,
    quotient_hasUniformConstitutiveWitness_iff
      Q M Mbar spec specbar m mbar F Fbar J Jbar ψ ψbar B₁ Bbar₁ C
  ]

end Metric

end RegimeSpecification

end PermanssonLean
