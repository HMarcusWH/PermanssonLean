import PermanssonResearch.ConstitutiveQuasi.PropertyErrors

/-!
# CQ-1 combined robust finite constitutive bounds

Reuses the *original* Proposition 5.2 output-error and uniform-margin
theorems. The original fixed comparison set B₁ is an evaluation domain,
not an automatically certified comparison set for the approximate baseline.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uS uX uA uH uC
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

/-- Concrete finite-path TV plus output errors transport the original
uniform margin to an approximation profile over the *same* frozen B₁. -/
theorem finiteConstitutiveMargin_lowerBound
    [MeasurableSpace.CountableOrCountablyGenerated
      (PermanssonLean.JointState S X) (PermanssonLean.JointState S X)]
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : StrategicApproximationPair M F J}
    {L : ℕ} {f : FinitePathProperty (PermanssonLean.JointState S X) L}
    {profile : PermanssonLean.RegimeSpecification.PerturbedPropertyProfile
      (PermanssonLean.JointState S X) ℝ}
    {eta : ℝ≥0∞} {κ δ₀ δJ b₀ bJ : ℝ}
    (certificate : FiniteConstitutiveCertificate M spec F B₁ J L f eta κ)
    (h : FinitePathModelErrors M spec F B₁ J pair L f profile δ₀ δJ b₀ bJ) :
    κ -
      (PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ₀ L + b₀ +
        (PermanssonLean.ProbabilitySupport.geometricTVEnvelope δJ L + bJ)) ≤
      PermanssonLean.RegimeSpecification.perturbedConstitutiveMargin
        M spec B₁ profile := by
  have houtput := h.toConstitutiveOutputErrors
  have hmargin := PermanssonLean.RegimeSpecification.perturbedConstitutiveMargin_ge
    M spec F (f.toRegimeProperty L) B₁ J profile
    (PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ₀ L + b₀)
    (PermanssonLean.ProbabilitySupport.geometricTVEnvelope δJ L + bJ) houtput
  exact (sub_le_sub_right certificate.marginFloor _).trans hmargin

/-- Strictly positive surviving margin is a meaningful finite robust
constitutive effect, not a claim that the approximate baseline is an Exact PR. -/
theorem finiteConstitutiveMargin_positive
    [MeasurableSpace.CountableOrCountablyGenerated
      (PermanssonLean.JointState S X) (PermanssonLean.JointState S X)]
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : StrategicApproximationPair M F J}
    {L : ℕ} {f : FinitePathProperty (PermanssonLean.JointState S X) L}
    {profile : PermanssonLean.RegimeSpecification.PerturbedPropertyProfile
      (PermanssonLean.JointState S X) ℝ}
    {eta : ℝ≥0∞} {κ δ₀ δJ b₀ bJ : ℝ}
    (certificate : FiniteConstitutiveCertificate M spec F B₁ J L f eta κ)
    (h : FinitePathModelErrors M spec F B₁ J pair L f profile δ₀ δJ b₀ bJ)
    (hbudget :
      PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ₀ L + b₀ +
        (PermanssonLean.ProbabilitySupport.geometricTVEnvelope δJ L + bJ) < κ) :
    0 < PermanssonLean.RegimeSpecification.perturbedConstitutiveMargin
      M spec B₁ profile := by
  have hlower := finiteConstitutiveMargin_lowerBound certificate h
  exact lt_of_lt_of_le (sub_pos.mpr hbudget) hlower

end ConstitutiveQuasi
end PermanssonResearch
