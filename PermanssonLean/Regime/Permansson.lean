import PermanssonLean.Regime.GeneratedRegime
import PermanssonLean.Regime.Constitution

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH uZ uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
variable [TopologicalSpace S] [TopologicalSpace X]

namespace RegimeSpecification

/-- Generalized Permansson status relative to one frozen constitutive protocol
(ψ, B₁, J): Exact GR plus pointwise strategic constitution under an admissible
strategic intervention with P held fixed by construction. -/
def IsGeneralizedPermanssonRegimeRelative
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) : Prop :=
  IsExactGeneratedRegime M spec m ∧
  IsStrategicallyConstitutive M spec F ψ B₁ J

/-- Definition 5.1 family form: an Exact GR is a generalized Permansson Regime
when at least one admissible predeclared strategic intervention in the frozen
family is constitutive for the declared property on B₁. -/
def IsGeneralizedPermanssonRegime
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) : Prop :=
  IsExactGeneratedRegime M spec m ∧
  ∃ J : AdmissibleStrategicIntervention F,
    IsStrategicallyConstitutive M spec F ψ B₁ J

theorem relativePR_exactGR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsGeneralizedPermanssonRegimeRelative M spec m F ψ B₁ J) :
    IsExactGeneratedRegime M spec m :=
  h.1

theorem relativePR_constitutive
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsGeneralizedPermanssonRegimeRelative M spec m F ψ B₁ J) :
    IsStrategicallyConstitutive M spec F ψ B₁ J :=
  h.2

theorem generalizedPR_exactGR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (h : IsGeneralizedPermanssonRegime M spec m F ψ B₁) :
    IsExactGeneratedRegime M spec m :=
  h.1

theorem generalizedPR_has_constitutive_intervention
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (h : IsGeneralizedPermanssonRegime M spec m F ψ B₁) :
    ∃ J : AdmissibleStrategicIntervention F,
      IsStrategicallyConstitutive M spec F ψ B₁ J :=
  h.2

theorem relativePR_implies_generalizedPR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsGeneralizedPermanssonRegimeRelative M spec m F ψ B₁ J) :
    IsGeneralizedPermanssonRegime M spec m F ψ B₁ := by
  exact ⟨h.1, ⟨J, h.2⟩⟩

/-- Every generalized-PR witness comes with an explicit theorem that the
world-transition kernel is held fixed. -/
theorem generalizedPR_world_fixed_witness
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (h : IsGeneralizedPermanssonRegime M spec m F ψ B₁) :
    ∃ J : AdmissibleStrategicIntervention F,
      IsStrategicallyConstitutive M spec F ψ B₁ J ∧
      J.intervention.apply.world = M.world := by
  rcases h.2 with ⟨J, hJ⟩
  exact ⟨J, hJ, J.world_eq⟩

end RegimeSpecification

end PermanssonLean
