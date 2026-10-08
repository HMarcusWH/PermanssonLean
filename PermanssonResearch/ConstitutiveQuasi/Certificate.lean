import PermanssonResearch.ConstitutiveQuasi.InterventionPair
import PermanssonResearch.ConstitutiveQuasi.SurvivalRobustness
import PermanssonLean.Regime.Perturbation
import PermanssonLean.Regime.QuasiStationary

/-!
# CQ-1: subordinate finite constitutive certificate

This finite-horizon proposition combines the *existing* region-wide
IsFinitePersistent gate and a positive uniform property margin on the frozen
path-law-nontrivial comparison set. It does not assert Exact GR, Exact PR, or QSD.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uS uX uA uH uC
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

/-- A nontrivial *finite* constitutive certificate, not an exact regime. The
frozen IsFinitePersistent gate is quantified over every state in spec.region;
the intervention margin uses the pre-verified B₁ comparison set. -/
structure FiniteConstitutiveCertificate
    (M : PermanssonLean.StrategicWorldModel S X A)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    {Component : Type uC}
    (F : PermanssonLean.InterventionFamily M Component)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec)
    (J : PermanssonLean.AdmissibleStrategicIntervention F)
    (L : ℕ) (f : FinitePathProperty (PermanssonLean.JointState S X) L)
    (eta : ℝ≥0∞) (κ : ℝ) : Prop where
  finitePersistent :
    PermanssonLean.RegimeSpecification.IsFinitePersistent M spec L eta
  positiveMargin : 0 < κ
  marginFloor :
    κ ≤ PermanssonLean.RegimeSpecification.constitutiveMargin M spec F
      (f.toRegimeProperty L) B₁ J

/-- A CQ-1 certificate implies uniform strategic constitution for the frozen
finite-path observable, but it does not claim exact GR/PR status. -/
theorem FiniteConstitutiveCertificate.uniformConstitution
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {L : ℕ} {f : FinitePathProperty (PermanssonLean.JointState S X) L}
    {eta : ℝ≥0∞} {κ : ℝ}
    (certificate : FiniteConstitutiveCertificate M spec F B₁ J L f eta κ) :
    PermanssonLean.RegimeSpecification.IsUniformlyStrategicallyConstitutive M spec
      F (f.toRegimeProperty L) B₁ J :=
  ⟨κ, certificate.positiveMargin, certificate.marginFloor⟩

end ConstitutiveQuasi
end PermanssonResearch
