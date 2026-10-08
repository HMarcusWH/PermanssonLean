import PermanssonResearch.ConstitutiveQuasi.CertificateTransport
import PermanssonResearch.ConstitutiveQuasi.Counterexamples

/-!
# CQ-1 Part 3 adversarial logical boundaries

No zero-horizon intervention can change a bounded finite-prefix observable
under a common point start. An approximation model with an altered world
primitive cannot be a shared-P strategic approximation pair.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uS uX uA uH uC
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- A common starting point makes the entire zero-horizon constitutive effect
identically zero, so strictly positive uniform constitution is impossible. -/
theorem noZeroHorizonFiniteConstitutiveCertificate
    (M : PermanssonLean.StrategicWorldModel S X A)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    {Component : Type uC}
    (F : PermanssonLean.InterventionFamily M Component)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec)
    (J : PermanssonLean.AdmissibleStrategicIntervention F)
    (f : FinitePathProperty (PermanssonLean.JointState S X) 0)
    (eta : ℝ≥0∞) (κ : ℝ) :
    ¬ FiniteConstitutiveCertificate M spec F B₁ J 0 f eta κ := by
  intro h
  obtain ⟨y, hy⟩ := B₁.states_nonempty
  have hle := PermanssonLean.RegimeSpecification.constitutiveMargin_le_effect
    M spec F (f.toRegimeProperty 0) B₁ J hy
  have hzero :
      PermanssonLean.RegimeSpecification.constitutiveEffect
        M (f.toRegimeProperty 0) J y = 0 := by
    unfold PermanssonLean.RegimeSpecification.constitutiveEffect
    rw [← finitePathExpectation_eq_baselineProperty M y 0 f,
      ← finitePathExpectation_eq_intervenedProperty J y 0 f]
    rw [expected_zero_independent_of_kernel
      M.inducedKernel J.intervention.apply.inducedKernel y f]
    simp
  have hk : κ ≤ 0 := (h.marginFloor.trans hle).trans_eq hzero
  exact (not_lt_of_ge hk) h.positiveMargin

/-- An explicit changed world primitive rules out any corresponding same-P
typed approximation object. A numerical kernel proximity is not a substitute. -/
theorem noStrategicApproximationPair_of_world_ne
    (M Mtilde : PermanssonLean.StrategicWorldModel S X A)
    {Component : Type uC}
    (F : PermanssonLean.InterventionFamily M Component)
    (J : PermanssonLean.AdmissibleStrategicIntervention F)
    (hne : Mtilde.world ≠ M.world) :
    ¬ ∃ pair : StrategicApproximationPair M F J, pair.approx = Mtilde := by
  rintro ⟨pair, hpair⟩
  apply hne
  rw [← hpair]
  exact pair.approx_world_eq

end ConstitutiveQuasi
end PermanssonResearch
