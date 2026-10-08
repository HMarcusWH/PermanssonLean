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

/-- A bundled CQ-1 certificate supplies a region-wide survival floor.
The baseline ENNReal gate is converted with the probability-measure finiteness
bound, then transferred using the already-proved finite-prefix event-TV law. -/
theorem finiteCertificate_survival_robust
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
    {eta : ℝ≥0∞} {κ δ₀ : ℝ}
    (certificate : FiniteConstitutiveCertificate M spec F B₁ J L f eta κ)
    (hδ₀ : 0 ≤ δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hTV : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.inducedKernel pair.approx.inducedKernel δ₀) :
    ∀ y ∈ spec.region,
      (1 - eta).toReal -
        PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ₀ L ≤
      (PermanssonLean.RegimeSpecification.survivalProbability
        pair.approx spec y L).toReal := by
  have hfloor : ∀ y ∈ spec.region,
      (1 - eta).toReal ≤
        (PermanssonLean.RegimeSpecification.survivalProbability M spec y L).toReal := by
    intro y hy
    exact ENNReal.toReal_mono (by finiteness)
      (certificate.finitePersistent.2 y hy)
  exact finiteSurvival_lower_of_prefixTV M pair.approx spec L
    (1 - eta).toReal hfloor hδ₀ hδ₀1 hTV

/-- Both robust bounds follow from the single frozen finite CQ-1 certificate,
the paired strategic models, and independent TV/output error ledgers. -/
theorem finiteConstitutiveCertificate_robust
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
    (∀ y ∈ spec.region,
      (1 - eta).toReal -
        PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ₀ L ≤
      (PermanssonLean.RegimeSpecification.survivalProbability
        pair.approx spec y L).toReal) ∧
    (κ -
      (PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ₀ L + b₀ +
        (PermanssonLean.ProbabilitySupport.geometricTVEnvelope δJ L + bJ)) ≤
      PermanssonLean.RegimeSpecification.perturbedConstitutiveMargin
        M spec B₁ profile) := by
  exact ⟨finiteCertificate_survival_robust certificate
      h.δ₀_nonneg h.δ₀_le_one h.tv_baseline,
    finiteConstitutiveMargin_lowerBound certificate h⟩

end ConstitutiveQuasi
end PermanssonResearch
