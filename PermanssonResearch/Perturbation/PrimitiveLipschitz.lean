import PermanssonResearch.Perturbation.PrimitiveMargin
import PermanssonResearch.ConstitutiveQuasi.PathOutput
import Mathlib.Tactic

/-!
# A2.3 generic finite-prefix total-variation Lipschitz property

The bounded-score case in PrimitiveMargin has factor one. The paper's more
general statement assumes a separate *explicit* finite-prefix functional
with a nonnegative Lipschitz constant in the event-supremum TV convention.
This module transports the genuine path-law property through original
Proposition 5.4 and Proposition 5.2 without claiming all properties are
Lipschitz or that positive margins imply an Exact Generated Regime.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace PermanssonResearch
namespace Perturbation

universe uS uX uA uH uZ

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MetricSpace Z]

variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.JointState S X) A]
variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.WorldInput S X A) X]
variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.UpdateInput S X A) S]
variable [MeasurableSpace.CountableOrCountablyGenerated
  (PermanssonLean.JointState S X) (PermanssonLean.JointState S X)]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- An explicitly TV-Lipschitz property of *measures of T-transition
prefixes*. `functional` may be nonlinear in the measure; this is NOT
restricted to expectations of unit-bounded scores. -/
structure TVLipschitzPrefixProperty
    (Y : Type*) [MeasurableSpace Y] (Z : Type*) [MetricSpace Z]
    (T : ℕ) where
  functional : Measure ((i : Finset.Iic T) → Y) → Z
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  lipschitz :
    ∀ (μ ν : Measure ((i : Finset.Iic T) → Y))
      [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      dist (functional μ) (functional ν) ≤
        constant * PermanssonLean.ProbabilitySupport.eventTotalVariation μ ν

/-- Turn the frozen T-prefix functional into the *original* whole-path
regime-property API, using no post-hoc descriptor. -/
noncomputable def TVLipschitzPrefixProperty.toRegimeProperty
    {Y : Type*} [MeasurableSpace Y] {Z : Type*} [MetricSpace Z]
    {T : ℕ} (p : TVLipschitzPrefixProperty Y Z T) :
    PermanssonLean.RegimePropertyMap Y Z :=
  fun law => p.functional (law.toMeasure.map (Preorder.frestrictLe T))

/-- Evaluate the original model's property on the true canonical T-prefix
law rather than an independently posited finite-state matrix. -/
theorem TVLipschitzPrefixProperty.baseline_eq_prefix
    {T : ℕ}
    (p : TVLipschitzPrefixProperty
      (PermanssonLean.JointState S X) Z T)
    (M : PermanssonLean.StrategicWorldModel S X A)
    (y : PermanssonLean.JointState S X) :
    PermanssonLean.RegimeSpecification.baselinePropertyValue
      p.toRegimeProperty M y =
    p.functional
      (PermanssonLean.ProbabilitySupport.finitePrefixLaw
        M.inducedKernel y T) := by
  change p.functional
    ((M.pathLaw (Measure.dirac y)).map (Preorder.frestrictLe T)) = _
  rw [PermanssonResearch.ConstitutiveQuasi.pathLaw_finitePrefix_eq]

theorem TVLipschitzPrefixProperty.intervened_eq_prefix
    {T : ℕ}
    (p : TVLipschitzPrefixProperty
      (PermanssonLean.JointState S X) Z T)
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type*}
    {F : PermanssonLean.InterventionFamily M Component}
    (J : PermanssonLean.AdmissibleStrategicIntervention F)
    (y : PermanssonLean.JointState S X) :
    PermanssonLean.RegimeSpecification.intervenedPropertyValue
      p.toRegimeProperty J.intervention y =
    p.functional
      (PermanssonLean.ProbabilitySupport.finitePrefixLaw
        J.intervention.apply.inducedKernel y T) := by
  change p.functional
    ((J.intervention.apply.pathLaw (Measure.dirac y)).map
      (Preorder.frestrictLe T)) = _
  rw [PermanssonResearch.ConstitutiveQuasi.pathLaw_finitePrefix_eq]

/-- Exact outputs of the second genuine typed model, not arbitrary numerical
reports. The baseline and intervened comparison must share a frozen protocol. -/
noncomputable def lipschitzApproximateProfile
    {T : ℕ}
    (p : TVLipschitzPrefixProperty
      (PermanssonLean.JointState S X) Z T)
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type*}
    {F : PermanssonLean.InterventionFamily M Component}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    (pair : PrimitiveModelPair M F J) :
    PermanssonLean.RegimeSpecification.PerturbedPropertyProfile
      (PermanssonLean.JointState S X) Z where
  baseline := fun y =>
    PermanssonLean.RegimeSpecification.baselinePropertyValue
      p.toRegimeProperty pair.approximate y
  intervention := fun y =>
    PermanssonLean.RegimeSpecification.intervenedPropertyValue
      p.toRegimeProperty pair.approximateIntervention.intervention y

/-- Required generic `Lψ`-TV-Lipschitz property: each model-output difference
is controlled by the independently derived primitive kernel error budget.
This theorem is conditional on the displayed Lipschitz certificate. -/
theorem TVLipschitzPrefixProperty.toOutputErrors
    {T : ℕ}
    (p : TVLipschitzPrefixProperty
      (PermanssonLean.JointState S X) Z T)
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification
      (PermanssonLean.JointState S X) H}
    {Component : Type*}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : PrimitiveModelPair M F J}
    (bounds : PrimitiveProtocolErrors M F J pair) :
    PermanssonLean.RegimeSpecification.HasConstitutiveOutputErrors
      M spec F p.toRegimeProperty B₁ J
      (lipschitzApproximateProfile p pair)
      (p.constant * bounds.baselinePrefixBudget T)
      (p.constant * bounds.interventionPrefixBudget T) := by
  have hbase_nonneg : 0 ≤ p.constant * bounds.baselinePrefixBudget T :=
    mul_nonneg p.constant_nonneg
      (PermanssonLean.ProbabilitySupport.geometricTVEnvelope_nonneg
        bounds.baseline.kernelBudget_nonneg
        bounds.baseline.kernelBudget_le_one T)
  have hJ_nonneg : 0 ≤ p.constant * bounds.interventionPrefixBudget T :=
    mul_nonneg p.constant_nonneg
      (PermanssonLean.ProbabilitySupport.geometricTVEnvelope_nonneg
        bounds.intervention.kernelBudget_nonneg
        bounds.intervention.kernelBudget_le_one T)
  refine ⟨hbase_nonneg, hJ_nonneg, ?_, ?_⟩
  · intro y hy
    change dist
      (PermanssonLean.RegimeSpecification.baselinePropertyValue
        p.toRegimeProperty M y)
      (PermanssonLean.RegimeSpecification.baselinePropertyValue
        p.toRegimeProperty pair.approximate y) ≤
      p.constant * bounds.baselinePrefixBudget T
    rw [p.baseline_eq_prefix M y, p.baseline_eq_prefix pair.approximate y]
    exact (p.lipschitz _ _).trans
      (mul_le_mul_of_nonneg_left
        (bounds.baseline.finitePrefix_tv y T) p.constant_nonneg)
  · intro y hy
    change dist
      (PermanssonLean.RegimeSpecification.intervenedPropertyValue
        p.toRegimeProperty J.intervention y)
      (PermanssonLean.RegimeSpecification.intervenedPropertyValue
        p.toRegimeProperty pair.approximateIntervention.intervention y) ≤
      p.constant * bounds.interventionPrefixBudget T
    rw [p.intervened_eq_prefix J y,
      p.intervened_eq_prefix pair.approximateIntervention y]
    exact (p.lipschitz _ _).trans
      (mul_le_mul_of_nonneg_left
        (bounds.intervention.finitePrefix_tv y T) p.constant_nonneg)

/-- The common frozen comparison states make the perturbed output-margin
definition identical to the actual second-model original-style margin. -/
theorem lipschitzApproximateProfile_margin_eq
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    {T : ℕ}
    (p : TVLipschitzPrefixProperty
      (PermanssonLean.JointState S X) Z T)
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification
      (PermanssonLean.JointState S X) H}
    {Component : Type*}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    (pair : PrimitiveModelPair M F J) :
    PermanssonLean.RegimeSpecification.perturbedConstitutiveMargin
      M spec B₁ (lipschitzApproximateProfile p pair) =
    PermanssonLean.RegimeSpecification.constitutiveMargin
      pair.approximate spec pair.approximateFamily p.toRegimeProperty
      (pair.comparisonSet spec B₁) pair.approximateIntervention := by
  rfl

/-- Proposed v0.2.0 Corollary 5.6 in the genuinely generic metric-valued,
TV-Lipschitz T-prefix subclass. Errors are computed independently on original
and matched intervened pairs; neither finite margin nor Lip condition
substitutes for the Exact-GR or empirical-identification gates. -/
theorem primitiveLipschitz_constitutiveMargin_abs_le
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    {T : ℕ}
    (p : TVLipschitzPrefixProperty
      (PermanssonLean.JointState S X) Z T)
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification
      (PermanssonLean.JointState S X) H}
    {Component : Type*}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : PrimitiveModelPair M F J}
    (bounds : PrimitiveProtocolErrors M F J pair) :
    |PermanssonLean.RegimeSpecification.constitutiveMargin
        pair.approximate spec pair.approximateFamily p.toRegimeProperty
        (pair.comparisonSet spec B₁) pair.approximateIntervention -
      PermanssonLean.RegimeSpecification.constitutiveMargin
        M spec F p.toRegimeProperty B₁ J| ≤
      p.constant * bounds.baselinePrefixBudget T +
        p.constant * bounds.interventionPrefixBudget T := by
  have h := PermanssonLean.RegimeSpecification.constitutiveMargin_perturbation_abs_le
    M spec F p.toRegimeProperty B₁ J
    (lipschitzApproximateProfile p pair)
    (p.constant * bounds.baselinePrefixBudget T)
    (p.constant * bounds.interventionPrefixBudget T)
    (p.toOutputErrors (B₁ := B₁) bounds)
  rwa [lipschitzApproximateProfile_margin_eq] at h

/-- The same v0.2.0 Lipschitz bound in its weaker, explicit linear
T-transition form, obtained from the original geometric Proposition 5.4.
The geometric estimate remains the preferred finite-horizon certificate. -/
theorem primitiveLipschitz_constitutiveMargin_le_linear
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    {T : ℕ}
    (p : TVLipschitzPrefixProperty
      (PermanssonLean.JointState S X) Z T)
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification
      (PermanssonLean.JointState S X) H}
    {Component : Type*}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : PrimitiveModelPair M F J}
    (bounds : PrimitiveProtocolErrors M F J pair) :
    |PermanssonLean.RegimeSpecification.constitutiveMargin
        pair.approximate spec pair.approximateFamily p.toRegimeProperty
        (pair.comparisonSet spec B₁) pair.approximateIntervention -
      PermanssonLean.RegimeSpecification.constitutiveMargin
        M spec F p.toRegimeProperty B₁ J| ≤
      p.constant * (T : ℝ) *
        (bounds.baseline.kernelBudget + bounds.intervention.kernelBudget) := by
  have hgeometry := primitiveLipschitz_constitutiveMargin_abs_le
    (M := M) (spec := spec) (F := F) (B₁ := B₁) (J := J)
    (pair := pair) p bounds
  have h0 := PermanssonLean.ProbabilitySupport.geometricTVEnvelope_le_linear
    bounds.baseline.kernelBudget_nonneg bounds.baseline.kernelBudget_le_one T
  have hJ := PermanssonLean.ProbabilitySupport.geometricTVEnvelope_le_linear
    bounds.intervention.kernelBudget_nonneg
    bounds.intervention.kernelBudget_le_one T
  calc
    _ ≤ p.constant * bounds.baselinePrefixBudget T +
        p.constant * bounds.interventionPrefixBudget T := hgeometry
    _ ≤ p.constant * ((T : ℝ) * bounds.baseline.kernelBudget) +
        p.constant * ((T : ℝ) * bounds.intervention.kernelBudget) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left h0 p.constant_nonneg)
            (mul_le_mul_of_nonneg_left hJ p.constant_nonneg)
    _ = _ := by ring

/-- A strictly positive finite-horizon uniform constitutive margin survives
when the *two independently certified* primitive model error budgets are
strictly below the original margin. The conclusion is not Exact GR or PR. -/
theorem primitiveLipschitz_positive_finiteMargin
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    {T : ℕ}
    (p : TVLipschitzPrefixProperty
      (PermanssonLean.JointState S X) Z T)
    {M : PermanssonLean.StrategicWorldModel S X A}
    {spec : PermanssonLean.RegimeSpecification
      (PermanssonLean.JointState S X) H}
    {Component : Type*}
    {F : PermanssonLean.InterventionFamily M Component}
    {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : PrimitiveModelPair M F J}
    (bounds : PrimitiveProtocolErrors M F J pair)
    (hgap : p.constant * bounds.baselinePrefixBudget T +
      p.constant * bounds.interventionPrefixBudget T <
        PermanssonLean.RegimeSpecification.constitutiveMargin
          M spec F p.toRegimeProperty B₁ J) :
    0 < PermanssonLean.RegimeSpecification.constitutiveMargin
      pair.approximate spec pair.approximateFamily p.toRegimeProperty
      (pair.comparisonSet spec B₁) pair.approximateIntervention := by
  have h := primitiveLipschitz_constitutiveMargin_abs_le
    (M := M) (spec := spec) (F := F) (B₁ := B₁) (J := J)
    (pair := pair) p bounds
  have hlower := (abs_le.mp h).1
  linarith

end Perturbation
end PermanssonResearch
