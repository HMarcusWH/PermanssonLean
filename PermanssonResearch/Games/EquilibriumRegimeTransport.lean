import PermanssonResearch.Perturbation.PrimitiveProductTV
import PermanssonResearch.Perturbation.ProductActionError
import PermanssonResearch.Perturbation.PrimitiveMargin
import PermanssonResearch.ConstitutiveQuasi.CertificateTransport
import Mathlib.Tactic

/-!
# Multiplicative primitive error to original constitutive margins
This is a composition of existing providers, with two separately typed budgets.
No regret-only bound, exact regime classification or occupation claim.
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

/-- A checked action-kernel discrepancy and literal equalities of P and U
construct the existing primitive record, rather than postulating a joint
kernel error or editing the original additive interface. -/
def fixedWorldUpdateBudget
    (M N : PermanssonLean.StrategicWorldModel S X A)
    (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1)
    (ha : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.generator.action N.generator.action δ)
    (hp : M.world = N.world)
    (hu : M.generator.update = N.generator.update) :
    PrimitiveErrorBounds M N where
  actionError := δ
  worldError := 0
  updateError := 0
  action_nonneg := h0
  action_le_one := h1
  world_nonneg := le_rfl
  world_le_one := by norm_num
  update_nonneg := le_rfl
  update_le_one := by norm_num
  action_tv := ha
  world_tv := by
    intro y
    rw [← hp]
    letI : IsMarkovKernel M.world := M.world_isMarkov
    rw [PermanssonLean.ProbabilitySupport.eventTotalVariation_self]
  update_tv := by
    intro y
    rw [← hu]
    letI : IsMarkovKernel M.generator.update := M.generator.update_isMarkov
    rw [PermanssonLean.ProbabilitySupport.eventTotalVariation_self]

/-- Retained primitive mass, with no independence assumption on the errors. -/
def PrimitiveErrorBounds.productBudget
    {M N : PermanssonLean.StrategicWorldModel S X A}
    (b : PrimitiveErrorBounds M N) : ℝ :=
  1-(1-b.actionError)*(1-b.worldError)*(1-b.updateError)

theorem PrimitiveErrorBounds.productBudget_nonneg
    {M N : PermanssonLean.StrategicWorldModel S X A}
    (b : PrimitiveErrorBounds M N) : 0 ≤ b.productBudget := by
  have ha : 0 ≤ 1-b.actionError := sub_nonneg.mpr b.action_le_one
  have hp : 0 ≤ 1-b.worldError := sub_nonneg.mpr b.world_le_one
  have hu : 0 ≤ 1-b.updateError := sub_nonneg.mpr b.update_le_one
  have hap : (1-b.actionError)*(1-b.worldError) ≤ 1 := by
    calc
      _ ≤ 1 * (1-b.worldError) := mul_le_mul_of_nonneg_right (by linarith [b.action_nonneg]) hp
      _ ≤ 1 := by linarith [b.world_nonneg]
  unfold PrimitiveErrorBounds.productBudget
  apply sub_nonneg.mpr
  calc
    _ ≤ 1 * (1-b.updateError) := mul_le_mul_of_nonneg_right hap hu
    _ ≤ 1 := by linarith [b.update_nonneg]

theorem PrimitiveErrorBounds.productBudget_le_one
    {M N : PermanssonLean.StrategicWorldModel S X A}
    (b : PrimitiveErrorBounds M N) : b.productBudget ≤ 1 := by
  unfold PrimitiveErrorBounds.productBudget
  have h := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr b.action_le_one) (sub_nonneg.mpr b.world_le_one))
    (sub_nonneg.mpr b.update_le_one)
  linarith

theorem PrimitiveErrorBounds.product_induced_tv
    {M N : PermanssonLean.StrategicWorldModel S X A}
    (b : PrimitiveErrorBounds M N) :
    PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.inducedKernel N.inducedKernel b.productBudget :=
  inducedKernel_tv_le_primitive_product M N
    b.action_nonneg b.action_le_one b.world_nonneg b.world_le_one
    b.update_nonneg b.update_le_one b.action_tv b.world_tv b.update_tv

def PrimitiveProtocolErrors.baselineProductPrefixBudget
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC} {F : PermanssonLean.InterventionFamily M Component}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : PrimitiveModelPair M F J}
    (b : PrimitiveProtocolErrors M F J pair) (T : ℕ) : ℝ :=
  PermanssonLean.ProbabilitySupport.geometricTVEnvelope b.baseline.productBudget T

noncomputable def PrimitiveProtocolErrors.interventionProductPrefixBudget
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC} {F : PermanssonLean.InterventionFamily M Component}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    {pair : PrimitiveModelPair M F J}
    (b : PrimitiveProtocolErrors M F J pair) (T : ℕ) : ℝ :=
  PermanssonLean.ProbabilitySupport.geometricTVEnvelope b.intervention.productBudget T

theorem PrimitiveProtocolErrors.toProductOutputErrors
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
      (bounds.baselineProductPrefixBudget T) (bounds.interventionProductPrefixBudget T) := by
  refine ⟨
    PermanssonLean.ProbabilitySupport.geometricTVEnvelope_nonneg
      bounds.baseline.productBudget_nonneg bounds.baseline.productBudget_le_one T,
    PermanssonLean.ProbabilitySupport.geometricTVEnvelope_nonneg
      bounds.intervention.productBudget_nonneg
      bounds.intervention.productBudget_le_one T, ?_, ?_⟩
  · intro y hy
    have h := PermanssonResearch.ConstitutiveQuasi.finitePathExpectation_abs_le_geometric
      M.inducedKernel pair.approximate.inducedKernel
      bounds.baseline.productBudget_nonneg bounds.baseline.productBudget_le_one
      bounds.baseline.product_induced_tv y T f
    change dist
      (PermanssonLean.RegimeSpecification.baselinePropertyValue
        (f.toRegimeProperty T) M y)
      (PermanssonLean.RegimeSpecification.baselinePropertyValue
        (f.toRegimeProperty T) pair.approximate y) ≤
        bounds.baselineProductPrefixBudget T
    rw [← PermanssonResearch.ConstitutiveQuasi.finitePathExpectation_eq_baselineProperty
        M y T f,
      ← PermanssonResearch.ConstitutiveQuasi.finitePathExpectation_eq_baselineProperty
        pair.approximate y T f, Real.dist_eq]
    exact h
  · intro y hy
    have h := PermanssonResearch.ConstitutiveQuasi.finitePathExpectation_abs_le_geometric
      J.intervention.apply.inducedKernel
      pair.approximateIntervention.intervention.apply.inducedKernel
      bounds.intervention.productBudget_nonneg
      bounds.intervention.productBudget_le_one
      bounds.intervention.product_induced_tv y T f
    change dist
      (PermanssonLean.RegimeSpecification.intervenedPropertyValue
        (f.toRegimeProperty T) J.intervention y)
      (PermanssonLean.RegimeSpecification.intervenedPropertyValue
        (f.toRegimeProperty T) pair.approximateIntervention.intervention y) ≤
        bounds.interventionProductPrefixBudget T
    rw [← PermanssonResearch.ConstitutiveQuasi.finitePathExpectation_eq_intervenedProperty
        J y T f,
      ← PermanssonResearch.ConstitutiveQuasi.finitePathExpectation_eq_intervenedProperty
        pair.approximateIntervention y T f, Real.dist_eq]
    exact h

theorem primitive_product_constitutiveMargin_abs_le
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
      bounds.baselineProductPrefixBudget T + bounds.interventionProductPrefixBudget T := by
  have h := PermanssonLean.RegimeSpecification.constitutiveMargin_perturbation_abs_le
    M spec F (f.toRegimeProperty T) B₁ J (exactApproximateProfile pair T f)
      (bounds.baselineProductPrefixBudget T) (bounds.interventionProductPrefixBudget T)
      (bounds.toProductOutputErrors T f)
  rwa [exactApproximateProfile_margin_eq] at h

/-- Lower-margin conclusion in the actual approximate model, without
changing the declared comparison domain or dropping either budget. -/
theorem primitive_product_constitutiveMargin_lower
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
    PermanssonLean.RegimeSpecification.constitutiveMargin M spec F
        (f.toRegimeProperty T) B₁ J -
        (bounds.baselineProductPrefixBudget T + bounds.interventionProductPrefixBudget T) ≤
      PermanssonLean.RegimeSpecification.constitutiveMargin pair.approximate spec
        pair.approximateFamily (f.toRegimeProperty T) (pair.comparisonSet spec B₁)
        pair.approximateIntervention := by
  have h := primitive_product_constitutiveMargin_abs_le
    (spec := spec) (B₁ := B₁) bounds T f
  linarith only [(abs_le.mp h).1]

end Perturbation
end PermanssonResearch
