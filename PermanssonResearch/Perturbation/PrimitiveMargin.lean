import PermanssonResearch.Perturbation.PrimitiveTV
import PermanssonResearch.ConstitutiveQuasi.CertificateTransport
import Mathlib.Tactic

/-!
# A2.2–A2.4: primitive model uncertainty to finite constitutive certificates

An accepted comparison contains TWO independent primitive-error budgets:
one for the genuine baseline models, one for their independently typed
admissible strategic interventions. Each strategic intervention fixes *its*
world kernel. The original and approximate world kernels may differ.

Finite-horizon positive margin is not an Exact Generated Regime. A full
CQ-1 finite constitutive certificate is promoted only when the original
region-wide finite-persistence premise is carried over as well.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace Perturbation

universe uS uX uA uC uH

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.JointState S X) A]
variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.WorldInput S X A) X]
variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.UpdateInput S X A) S]
variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.JointState S X) (PermanssonLean.JointState S X)]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- Typed pointwise *global* primitive error bounds. These are model-pair
hypotheses, not derived by reading a JSON report or sampling a finite grid. -/
structure PrimitiveErrorBounds
    (M N : PermanssonLean.StrategicWorldModel S X A) where
  actionError : ℝ
  worldError : ℝ
  updateError : ℝ
  action_nonneg : 0 ≤ actionError
  action_le_one : actionError ≤ 1
  world_nonneg : 0 ≤ worldError
  world_le_one : worldError ≤ 1
  update_nonneg : 0 ≤ updateError
  update_le_one : updateError ≤ 1
  action_tv :
    PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.generator.action N.generator.action actionError
  world_tv :
    PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.world N.world worldError
  update_tv :
    PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.generator.update N.generator.update updateError

/-- Uniform induced-kernel upper budget. -/
def PrimitiveErrorBounds.kernelBudget
    {M N : PermanssonLean.StrategicWorldModel S X A}
    (bounds : PrimitiveErrorBounds M N) : ℝ :=
  min 1 (bounds.actionError + bounds.worldError + bounds.updateError)

theorem PrimitiveErrorBounds.kernelBudget_nonneg
    {M N : PermanssonLean.StrategicWorldModel S X A}
    (bounds : PrimitiveErrorBounds M N) :
    0 ≤ bounds.kernelBudget := by
  unfold PrimitiveErrorBounds.kernelBudget
  exact le_min (by norm_num)
    (add_nonneg (add_nonneg bounds.action_nonneg bounds.world_nonneg)
      bounds.update_nonneg)

theorem PrimitiveErrorBounds.kernelBudget_le_one
    {M N : PermanssonLean.StrategicWorldModel S X A}
    (bounds : PrimitiveErrorBounds M N) :
    bounds.kernelBudget ≤ 1 :=
  min_le_left _ _

/-- A2.1 discharges the original finite-path theory's uniform-kernel
error hypothesis using *primitive* rather than postulated joint budgets. -/
theorem PrimitiveErrorBounds.induced_tv
    {M N : PermanssonLean.StrategicWorldModel S X A}
    (bounds : PrimitiveErrorBounds M N) :
    PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.inducedKernel N.inducedKernel bounds.kernelBudget := by
  exact inducedKernel_tv_le_primitive_sum M N
    bounds.action_nonneg bounds.action_le_one
    bounds.world_nonneg bounds.world_le_one
    bounds.update_nonneg bounds.update_le_one
    bounds.action_tv bounds.world_tv bounds.update_tv

/-- A2.2: the real canonical finite-prefix law (0 through T) satisfies the
existing geometric TV envelope, now with a *derived primitive* budget. -/
theorem PrimitiveErrorBounds.finitePrefix_tv
    {M N : PermanssonLean.StrategicWorldModel S X A}
    (bounds : PrimitiveErrorBounds M N)
    (y : PermanssonLean.JointState S X) (T : ℕ) :
    PermanssonLean.ProbabilitySupport.eventTotalVariation
      (PermanssonLean.ProbabilitySupport.finitePrefixLaw
        M.inducedKernel y T)
      (PermanssonLean.ProbabilitySupport.finitePrefixLaw
        N.inducedKernel y T) ≤
      PermanssonLean.ProbabilitySupport.geometricTVEnvelope
        bounds.kernelBudget T :=
  PermanssonLean.ProbabilitySupport.finitePrefix_eventTotalVariation_le_geometric
    M.inducedKernel N.inducedKernel
    bounds.kernelBudget_nonneg bounds.kernelBudget_le_one
    bounds.induced_tv y T

theorem PrimitiveErrorBounds.finitePrefix_tv_le_linear
    {M N : PermanssonLean.StrategicWorldModel S X A}
    (bounds : PrimitiveErrorBounds M N)
    (y : PermanssonLean.JointState S X) (T : ℕ) :
    PermanssonLean.ProbabilitySupport.eventTotalVariation
      (PermanssonLean.ProbabilitySupport.finitePrefixLaw
        M.inducedKernel y T)
      (PermanssonLean.ProbabilitySupport.finitePrefixLaw
        N.inducedKernel y T) ≤
      (T : ℝ) * bounds.kernelBudget :=
  PermanssonLean.ProbabilitySupport.finitePrefix_eventTotalVariation_le_linear
    M.inducedKernel N.inducedKernel
    bounds.kernelBudget_nonneg bounds.kernelBudget_le_one
    bounds.induced_tv y T

/-- Two independently checked primitive comparisons, both using the actual
action/world/update kernels *after* their matched strategic interventions. -/
structure PrimitiveProtocolErrors
    (M : PermanssonLean.StrategicWorldModel S X A)
    {Component : Type uC}
    (F : PermanssonLean.InterventionFamily M Component)
    (J : PermanssonLean.AdmissibleStrategicIntervention F)
    (pair : PrimitiveModelPair M F J) where
  baseline : PrimitiveErrorBounds M pair.approximate
  intervention : PrimitiveErrorBounds
    J.intervention.apply pair.approximateIntervention.intervention.apply

/-- Source-normalized geometric finite-prefix error (T transitions). -/
def PrimitiveProtocolErrors.baselinePrefixBudget
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : PrimitiveModelPair M F J}
    (bounds : PrimitiveProtocolErrors M F J pair) (T : ℕ) : ℝ :=
  PermanssonLean.ProbabilitySupport.geometricTVEnvelope
    bounds.baseline.kernelBudget T

noncomputable def PrimitiveProtocolErrors.interventionPrefixBudget
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : PrimitiveModelPair M F J}
    (bounds : PrimitiveProtocolErrors M F J pair) (T : ℕ) : ℝ :=
  PermanssonLean.ProbabilitySupport.geometricTVEnvelope
    bounds.intervention.kernelBudget T

/-- The actual second-model path-law output profile, with no numerical
evaluation error. This is not an independently supplied approximation. -/
noncomputable def exactApproximateProfile
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    (pair : PrimitiveModelPair M F J)
    (T : ℕ)
    (f : PermanssonResearch.ConstitutiveQuasi.FinitePathProperty
      (PermanssonLean.JointState S X) T) :
    PermanssonLean.RegimeSpecification.PerturbedPropertyProfile
      (PermanssonLean.JointState S X) ℝ where
  baseline := fun y =>
    PermanssonLean.RegimeSpecification.baselinePropertyValue
      (f.toRegimeProperty T) pair.approximate y
  intervention := fun y =>
    PermanssonLean.RegimeSpecification.intervenedPropertyValue
      (f.toRegimeProperty T) pair.approximateIntervention.intervention y

/-- Bridge from two primitive row-budget sets to original Proposition 5.2's
two-sided *genuine model output* error interface. -/
theorem PrimitiveProtocolErrors.toOutputErrors
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : PrimitiveModelPair M F J}
    (bounds : PrimitiveProtocolErrors M F J pair)
    (T : ℕ)
    (f : PermanssonResearch.ConstitutiveQuasi.FinitePathProperty
      (PermanssonLean.JointState S X) T) :
    PermanssonLean.RegimeSpecification.HasConstitutiveOutputErrors
      M spec F (f.toRegimeProperty T) B₁ J
      (exactApproximateProfile pair T f)
      (bounds.baselinePrefixBudget T) (bounds.interventionPrefixBudget T) := by
  refine ⟨
    PermanssonLean.ProbabilitySupport.geometricTVEnvelope_nonneg
      bounds.baseline.kernelBudget_nonneg bounds.baseline.kernelBudget_le_one T,
    PermanssonLean.ProbabilitySupport.geometricTVEnvelope_nonneg
      bounds.intervention.kernelBudget_nonneg
      bounds.intervention.kernelBudget_le_one T, ?_, ?_⟩
  · intro y hy
    have h := PermanssonResearch.ConstitutiveQuasi.finitePathExpectation_abs_le_geometric
      M.inducedKernel pair.approximate.inducedKernel
      bounds.baseline.kernelBudget_nonneg bounds.baseline.kernelBudget_le_one
      bounds.baseline.induced_tv y T f
    change dist
      (PermanssonLean.RegimeSpecification.baselinePropertyValue
        (f.toRegimeProperty T) M y)
      (PermanssonLean.RegimeSpecification.baselinePropertyValue
        (f.toRegimeProperty T) pair.approximate y) ≤
        bounds.baselinePrefixBudget T
    rw [← PermanssonResearch.ConstitutiveQuasi.finitePathExpectation_eq_baselineProperty
        M y T f,
      ← PermanssonResearch.ConstitutiveQuasi.finitePathExpectation_eq_baselineProperty
        pair.approximate y T f, Real.dist_eq]
    exact h
  · intro y hy
    have h := PermanssonResearch.ConstitutiveQuasi.finitePathExpectation_abs_le_geometric
      J.intervention.apply.inducedKernel
      pair.approximateIntervention.intervention.apply.inducedKernel
      bounds.intervention.kernelBudget_nonneg
      bounds.intervention.kernelBudget_le_one
      bounds.intervention.induced_tv y T f
    change dist
      (PermanssonLean.RegimeSpecification.intervenedPropertyValue
        (f.toRegimeProperty T) J.intervention y)
      (PermanssonLean.RegimeSpecification.intervenedPropertyValue
        (f.toRegimeProperty T) pair.approximateIntervention.intervention y) ≤
        bounds.interventionPrefixBudget T
    rw [← PermanssonResearch.ConstitutiveQuasi.finitePathExpectation_eq_intervenedProperty
        J y T f,
      ← PermanssonResearch.ConstitutiveQuasi.finitePathExpectation_eq_intervenedProperty
        pair.approximateIntervention y T f, Real.dist_eq]
    exact h

/-- The comparison set's *states* are transported unchanged; this equality
identifies the second model's real original-style margin, not merely a profile
number on a different basin. -/
theorem exactApproximateProfile_margin_eq
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    (pair : PrimitiveModelPair M F J)
    (T : ℕ)
    (f : PermanssonResearch.ConstitutiveQuasi.FinitePathProperty
      (PermanssonLean.JointState S X) T) :
    PermanssonLean.RegimeSpecification.perturbedConstitutiveMargin
      M spec B₁ (exactApproximateProfile pair T f) =
    PermanssonLean.RegimeSpecification.constitutiveMargin
      pair.approximate spec pair.approximateFamily
      (f.toRegimeProperty T) (pair.comparisonSet spec B₁)
      pair.approximateIntervention := by
  rfl

/-- A2 Corollary 5.6 (factor-one bounded finite-path property): the actual
original and approximate uniform constitutive margins are within the two
separately derived geometric primitive error envelopes. -/
theorem primitive_constitutiveMargin_abs_le
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : PrimitiveModelPair M F J}
    (bounds : PrimitiveProtocolErrors M F J pair)
    (T : ℕ)
    (f : PermanssonResearch.ConstitutiveQuasi.FinitePathProperty
      (PermanssonLean.JointState S X) T) :
    |PermanssonLean.RegimeSpecification.constitutiveMargin
        pair.approximate spec pair.approximateFamily
        (f.toRegimeProperty T) (pair.comparisonSet spec B₁)
        pair.approximateIntervention -
      PermanssonLean.RegimeSpecification.constitutiveMargin
        M spec F (f.toRegimeProperty T) B₁ J| ≤
      bounds.baselinePrefixBudget T + bounds.interventionPrefixBudget T := by
  have h := PermanssonLean.RegimeSpecification.constitutiveMargin_perturbation_abs_le
    M spec F (f.toRegimeProperty T) B₁ J (exactApproximateProfile pair T f)
      (bounds.baselinePrefixBudget T) (bounds.interventionPrefixBudget T)
      (bounds.toOutputErrors T f)
  rwa [exactApproximateProfile_margin_eq] at h

/-- Positive genuine finite-horizon margin survives the *two* primitive
error budgets. No Exact-GR conclusion. -/
theorem primitive_positive_finiteMargin
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : PrimitiveModelPair M F J}
    (bounds : PrimitiveProtocolErrors M F J pair)
    (T : ℕ)
    (f : PermanssonResearch.ConstitutiveQuasi.FinitePathProperty
      (PermanssonLean.JointState S X) T)
    (hgap :
      bounds.baselinePrefixBudget T + bounds.interventionPrefixBudget T <
        PermanssonLean.RegimeSpecification.constitutiveMargin
          M spec F (f.toRegimeProperty T) B₁ J) :
    0 < PermanssonLean.RegimeSpecification.constitutiveMargin
      pair.approximate spec pair.approximateFamily
      (f.toRegimeProperty T) (pair.comparisonSet spec B₁)
      pair.approximateIntervention := by
  have h := primitive_constitutiveMargin_abs_le
    (M := M) (spec := spec) (F := F) (B₁ := B₁) (J := J)
    (pair := pair) bounds T f
  have hright := (abs_le.mp h).2
  linarith

/-- Complete CQ-1 finite constitutive certificate: transfer BOTH the
region-wide finite-persistence lower bound and the positive genuine effect
margin to the new typed model. The approximation may have a different P.
This is NOT a certified Exact GR, Exact PR, or QSD. -/
theorem transportPrimitiveFiniteConstitutiveCertificate
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : PrimitiveModelPair M F J}
    (bounds : PrimitiveProtocolErrors M F J pair)
    {T : ℕ}
    {f : PermanssonResearch.ConstitutiveQuasi.FinitePathProperty
      (PermanssonLean.JointState S X) T}
    {eta : ℝ≥0∞} {κ : ℝ}
    (certificate :
      PermanssonResearch.ConstitutiveQuasi.FiniteConstitutiveCertificate
        M spec F B₁ J T f eta κ)
    (hremaining :
      bounds.baselinePrefixBudget T + bounds.interventionPrefixBudget T < κ) :
    PermanssonResearch.ConstitutiveQuasi.FiniteConstitutiveCertificate
      pair.approximate spec pair.approximateFamily
      (pair.comparisonSet spec B₁) pair.approximateIntervention T f
      (PermanssonResearch.ConstitutiveQuasi.clampedPersistenceError
        eta (bounds.baselinePrefixBudget T))
      (κ - bounds.baselinePrefixBudget T -
        bounds.interventionPrefixBudget T) := by
  let e₀ := bounds.baselinePrefixBudget T
  let eJ := bounds.interventionPrefixBudget T
  have he₀ : 0 ≤ e₀ :=
    PermanssonLean.ProbabilitySupport.geometricTVEnvelope_nonneg
      bounds.baseline.kernelBudget_nonneg
      bounds.baseline.kernelBudget_le_one T
  have hsurvival :
      PermanssonLean.RegimeSpecification.IsFinitePersistent pair.approximate spec T
        (PermanssonResearch.ConstitutiveQuasi.clampedPersistenceError eta e₀) := by
    apply PermanssonResearch.ConstitutiveQuasi.finitePersistence_of_real_error
      pair.approximate spec T eta certificate.finitePersistent.1 e₀ he₀
    exact PermanssonResearch.ConstitutiveQuasi.finiteSurvival_lower_of_prefixTV
      M pair.approximate spec T (1 - eta).toReal
      (by
        intro y hy
        exact ENNReal.toReal_mono
          (MeasureTheory.measure_ne_top
            (M.pathLaw (Measure.dirac y))
            (PermanssonLean.RegimeSpecification.survivesThroughSet spec T))
          (certificate.finitePersistent.2 y hy))
      bounds.baseline.kernelBudget_nonneg
      bounds.baseline.kernelBudget_le_one
      bounds.baseline.induced_tv
  have hmargin := primitive_constitutiveMargin_abs_le
    (M := M) (spec := spec) (F := F) (B₁ := B₁) (J := J)
    (pair := pair) bounds T f
  have hupper := (abs_le.mp hmargin).2
  have hbound :
      κ - e₀ - eJ ≤
        PermanssonLean.RegimeSpecification.constitutiveMargin
          pair.approximate spec pair.approximateFamily
          (f.toRegimeProperty T) (pair.comparisonSet spec B₁)
          pair.approximateIntervention := by
    dsimp [e₀, eJ]
    linarith [certificate.marginFloor]
  exact ⟨hsurvival, by dsimp [e₀, eJ]; linarith, hbound⟩

/-- A2.4: optional independently bounded numerical/reporting profile.
These extra b0/bJ uncertainties are separate from the exact second-model
errors; the reported profile is NOT automatically that model's exact margin. -/
theorem reportedPrimitiveMargin_abs_le
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : PrimitiveModelPair M F J}
    (bounds : PrimitiveProtocolErrors M F J pair)
    (T : ℕ)
    (f : PermanssonResearch.ConstitutiveQuasi.FinitePathProperty
      (PermanssonLean.JointState S X) T)
    (report : PermanssonLean.RegimeSpecification.PerturbedPropertyProfile
      (PermanssonLean.JointState S X) ℝ)
    {b₀ bJ : ℝ} (hb₀ : 0 ≤ b₀) (hbJ : 0 ≤ bJ)
    (hreport₀ : ∀ y ∈ B₁.states,
      dist ((exactApproximateProfile pair T f).baseline y) (report.baseline y) ≤ b₀)
    (hreportJ : ∀ y ∈ B₁.states,
      dist ((exactApproximateProfile pair T f).intervention y)
        (report.intervention y) ≤ bJ) :
    |PermanssonLean.RegimeSpecification.perturbedConstitutiveMargin
        M spec B₁ report -
      PermanssonLean.RegimeSpecification.constitutiveMargin
        M spec F (f.toRegimeProperty T) B₁ J| ≤
      (bounds.baselinePrefixBudget T + b₀) +
        (bounds.interventionPrefixBudget T + bJ) := by
  have hmodel := bounds.toOutputErrors (spec := spec) (B₁ := B₁) T f
  have houtput : PermanssonLean.RegimeSpecification.HasConstitutiveOutputErrors
      M spec F (f.toRegimeProperty T) B₁ J report
      (bounds.baselinePrefixBudget T + b₀)
      (bounds.interventionPrefixBudget T + bJ) := by
    refine ⟨add_nonneg hmodel.baseline_nonneg hb₀,
      add_nonneg hmodel.intervention_nonneg hbJ, ?_, ?_⟩
    · intro y hy
      calc
        dist (PermanssonLean.RegimeSpecification.baselinePropertyValue
            (f.toRegimeProperty T) M y) (report.baseline y) ≤
            dist (PermanssonLean.RegimeSpecification.baselinePropertyValue
              (f.toRegimeProperty T) M y)
              ((exactApproximateProfile pair T f).baseline y) +
            dist ((exactApproximateProfile pair T f).baseline y)
              (report.baseline y) := dist_triangle _ _ _
        _ ≤ bounds.baselinePrefixBudget T + b₀ :=
          add_le_add (hmodel.baseline_le y hy) (hreport₀ y hy)
    · intro y hy
      calc
        dist (PermanssonLean.RegimeSpecification.intervenedPropertyValue
            (f.toRegimeProperty T) J.intervention y)
            (report.intervention y) ≤
            dist (PermanssonLean.RegimeSpecification.intervenedPropertyValue
              (f.toRegimeProperty T) J.intervention y)
              ((exactApproximateProfile pair T f).intervention y) +
            dist ((exactApproximateProfile pair T f).intervention y)
              (report.intervention y) := dist_triangle _ _ _
        _ ≤ bounds.interventionPrefixBudget T + bJ :=
          add_le_add (hmodel.intervention_le y hy) (hreportJ y hy)
  exact PermanssonLean.RegimeSpecification.constitutiveMargin_perturbation_abs_le
    M spec F (f.toRegimeProperty T) B₁ J report
    (bounds.baselinePrefixBudget T + b₀)
    (bounds.interventionPrefixBudget T + bJ) houtput

end Perturbation
end PermanssonResearch
