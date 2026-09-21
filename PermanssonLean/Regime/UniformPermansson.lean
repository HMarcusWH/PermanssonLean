import PermanssonLean.Regime.Permansson
import PermanssonLean.Regime.Perturbation

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH uZ uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
variable [TopologicalSpace S] [TopologicalSpace X]
variable [MetricSpace Z]

namespace RegimeSpecification

/-- Quantitative generalized Permansson status relative to one frozen
constitutive protocol.  This strengthens pointwise constitution with a
strictly positive uniform constitutive margin. -/
def IsUniformGeneralizedPermanssonRegimeRelative
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) : Prop :=
  IsExactGeneratedRegime M spec m ∧
  IsUniformlyStrategicallyConstitutive M spec F ψ B₁ J

/-- Family-level quantitative PR certificate: at least one admissible
predeclared strategic intervention has positive uniform margin. -/
def IsUniformGeneralizedPermanssonRegime
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) : Prop :=
  IsExactGeneratedRegime M spec m ∧
  ∃ J : AdmissibleStrategicIntervention F,
    IsUniformlyStrategicallyConstitutive M spec F ψ B₁ J

theorem uniformRelativePR_exactGR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsUniformGeneralizedPermanssonRegimeRelative M spec m F ψ B₁ J) :
    IsExactGeneratedRegime M spec m :=
  h.1

theorem uniformRelativePR_margin_pos
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsUniformGeneralizedPermanssonRegimeRelative M spec m F ψ B₁ J) :
    0 < constitutiveMargin M spec F ψ B₁ J :=
  (uniformlyConstitutive_iff_margin_pos M spec F ψ B₁ J).1 h.2

theorem uniformRelativePR_implies_relativePR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsUniformGeneralizedPermanssonRegimeRelative M spec m F ψ B₁ J) :
    IsGeneralizedPermanssonRegimeRelative M spec m F ψ B₁ J := by
  exact ⟨h.1, uniformlyConstitutive_implies_constitutive M spec F ψ B₁ J h.2⟩

theorem uniformGeneralizedPR_exactGR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (h : IsUniformGeneralizedPermanssonRegime M spec m F ψ B₁) :
    IsExactGeneratedRegime M spec m :=
  h.1

/-- Quantitative PR status is a strict strengthening of generalized PR status:
positive uniform margin implies pointwise constitution for the same witness. -/
theorem uniformGeneralizedPR_implies_generalizedPR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (h : IsUniformGeneralizedPermanssonRegime M spec m F ψ B₁) :
    IsGeneralizedPermanssonRegime M spec m F ψ B₁ := by
  rcases h.2 with ⟨J, hJ⟩
  exact ⟨h.1, ⟨J,
    uniformlyConstitutive_implies_constitutive M spec F ψ B₁ J hJ⟩⟩

/-- Robustness certificate attached to an already certified uniform PR
protocol.  The conclusion deliberately preserves only the baseline Exact-GR
certificate together with positivity of the perturbed constitutive margin; it
does not claim that the approximate profile itself comes from another GR. -/
theorem robustUniformPRCertificate
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (profile : PerturbedPropertyProfile (JointState S X) Z)
    (ε₀ εJ : ℝ)
    (hPR : IsUniformGeneralizedPermanssonRegimeRelative M spec m F ψ B₁ J)
    (hErr : HasConstitutiveOutputErrors M spec F ψ B₁ J profile ε₀ εJ)
    (hgap :
      ε₀ + εJ < constitutiveMargin M spec F ψ B₁ J) :
    IsExactGeneratedRegime M spec m ∧
      0 < perturbedConstitutiveMargin M spec B₁ profile := by
  exact ⟨hPR.1,
    robustUniformConstitution M spec F ψ B₁ J profile ε₀ εJ hErr hgap⟩

end RegimeSpecification

end PermanssonLean
