import PermanssonResearch.ConstitutiveQuasi.ComparisonTransport
import PermanssonResearch.ConstitutiveQuasi.PersistencePromotion
import PermanssonResearch.ConstitutiveQuasi.PropertyErrors

/-!
# CQ-1 Part 3: transport of the typed finite constitutive certificate

Unlike a numerical output-profile bound, this theorem produces a genuine
FiniteConstitutiveCertificate for the second strategic-world model. It requires
the same P, separate pointwise-global one-step TV bounds, and a strictly
positive true-model effect margin after finite-horizon propagation.
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

/-- True exact finite-path expectations under the *approximate* strategic
baseline and admissible strategic intervention. No numerical output-error
parameter appears in these model-defined outputs. -/
noncomputable def modelExactOutputProfile
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    (pair : StrategicApproximationPair M F J)
    (L : ℕ) (f : FinitePathProperty (PermanssonLean.JointState S X) L) :
    PermanssonLean.RegimeSpecification.PerturbedPropertyProfile
      (PermanssonLean.JointState S X) ℝ where
  baseline := fun y =>
    PermanssonLean.RegimeSpecification.baselinePropertyValue
      (f.toRegimeProperty L) pair.approx y
  intervention := fun y =>
    PermanssonLean.RegimeSpecification.intervenedPropertyValue
      (f.toRegimeProperty L) pair.approxIntervention.intervention y

/-- The true output profile consumes no numerical output error.
Kernel approximation is instead accounted for by the two TV hypotheses. -/
theorem modelExactOutputProfile_errors
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    (pair : StrategicApproximationPair M F J)
    (L : ℕ) (f : FinitePathProperty (PermanssonLean.JointState S X) L)
    {δ₀ δJ : ℝ}
    (hδ₀ : 0 ≤ δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hδJ : 0 ≤ δJ) (hδJ1 : δJ ≤ 1)
    (hTV₀ : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.inducedKernel pair.approx.inducedKernel δ₀)
    (hTVJ : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      J.intervention.apply.inducedKernel
      pair.approxIntervention.intervention.apply.inducedKernel δJ) :
    FinitePathModelErrors M spec F B₁ J pair L f
      (modelExactOutputProfile pair L f) δ₀ δJ 0 0 := by
  refine ⟨hδ₀, hδ₀1, hδJ, hδJ1,
    le_refl _, le_refl _, hTV₀, hTVJ, ?_, ?_⟩
  · intro y hy
    rw [finitePathExpectation_eq_baselineProperty pair.approx y L f]
    simp [modelExactOutputProfile]
  · intro y hy
    rw [finitePathExpectation_eq_intervenedProperty pair.approxIntervention y L f]
    simp [modelExactOutputProfile]

/-- The original frozen B₁ set is definitionally the same evaluation domain
after transport, so the exact output profile's infimum is the genuine
constitutive margin of the second model. -/
theorem modelExactOutputProfile_margin_eq
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    (pair : StrategicApproximationPair M F J)
    (L : ℕ) (f : FinitePathProperty (PermanssonLean.JointState S X) L) :
    PermanssonLean.RegimeSpecification.perturbedConstitutiveMargin
      M spec B₁ (modelExactOutputProfile pair L f) =
    PermanssonLean.RegimeSpecification.constitutiveMargin pair.approx spec
      pair.approxFamily (f.toRegimeProperty L)
      (transportComparisonSet M pair.approx spec B₁)
      pair.approxIntervention := by
  rfl

/-- Transport CQ-1 to a different strategic model sharing the original P,
with a clamped admissible persistence error and strictly positive genuine
finite-path constitutive margin. This is not an Exact GR/PR transfer. -/
theorem transportFiniteConstitutiveCertificate
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
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
    {eta : ℝ≥0∞} {κ δ₀ δJ : ℝ}
    (certificate : FiniteConstitutiveCertificate M spec F B₁ J L f eta κ)
    (hδ₀ : 0 ≤ δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hδJ : 0 ≤ δJ) (hδJ1 : δJ ≤ 1)
    (hTV₀ : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.inducedKernel pair.approx.inducedKernel δ₀)
    (hTVJ : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      J.intervention.apply.inducedKernel
      pair.approxIntervention.intervention.apply.inducedKernel δJ)
    (hremaining :
      PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ₀ L +
        PermanssonLean.ProbabilitySupport.geometricTVEnvelope δJ L < κ) :
    FiniteConstitutiveCertificate
      pair.approx spec pair.approxFamily
      (transportComparisonSet M pair.approx spec B₁)
      pair.approxIntervention L f
      (clampedPersistenceError eta
        (PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ₀ L))
      (κ - PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ₀ L -
        PermanssonLean.ProbabilitySupport.geometricTVEnvelope δJ L) := by
  let e₀ := PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ₀ L
  let eJ := PermanssonLean.ProbabilitySupport.geometricTVEnvelope δJ L
  have he₀ : 0 ≤ e₀ :=
    PermanssonLean.ProbabilitySupport.geometricTVEnvelope_nonneg hδ₀ hδ₀1 L
  have hsurvival :
      PermanssonLean.RegimeSpecification.IsFinitePersistent pair.approx spec L
        (clampedPersistenceError eta e₀) := by
    apply finitePersistence_of_real_error pair.approx spec L eta
      certificate.finitePersistent.1 e₀ he₀
    exact finiteCertificate_survival_robust certificate hδ₀ hδ₀1 hTV₀
  have herr := modelExactOutputProfile_errors
    (M := M) (spec := spec) (F := F) (B₁ := B₁) (J := J)
    pair L f hδ₀ hδ₀1 hδJ hδJ1 hTV₀ hTVJ
  have hgap := finiteConstitutiveMargin_lowerBound certificate herr
  rw [modelExactOutputProfile_margin_eq] at hgap
  have hmargin :
      κ - e₀ - eJ ≤
      PermanssonLean.RegimeSpecification.constitutiveMargin pair.approx spec
        pair.approxFamily (f.toRegimeProperty L)
        (transportComparisonSet M pair.approx spec B₁)
        pair.approxIntervention := by
    dsimp [e₀, eJ]
    convert hgap using 1 <;> ring
  exact ⟨hsurvival, by linarith, hmargin⟩

end ConstitutiveQuasi
end PermanssonResearch
