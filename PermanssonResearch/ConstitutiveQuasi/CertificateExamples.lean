import PermanssonResearch.ConstitutiveQuasi.Robustness
import PermanssonLean.Examples.ConstitutiveNoninvariance
import PermanssonResearch.ConstitutiveQuasi.Counterexamples

/-!
# CQ-1 Part 2 positive typed finite witness

Reuse the frozen finite modelB: starting in x=false it survives one
transition with probability one; its admissible action-selection intervention
exits to x=true immediately. The world primitive P is unchanged by that
intervention. The new bounded finite-path score is the prefix survival event.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace ConstitutiveQuasi
namespace CertificateExamples

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonLean.Section7ConstitutiveNoninvariance

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- The original path-law-nontrivial comparison domain, checked against the
one-step survival specification rather than the unrelated Exact GR spec. -/
def comparisonStay : ConstitutiveComparisonSet modelB stayFalseSpec where
  states := comparisonB.states
  states_measurable := comparisonB.states_measurable
  states_subset_basin := by
    intro y hy
    exact comparisonB.states_subset_basin hy
  pathLawNontrivial := comparisonB.pathLawNontrivial

/-- The measurable [0,1] score of staying inside B at times 0 and 1. -/
noncomputable def finiteSurvivalScore :
    FinitePathProperty (JointState Bool Bool) 1 where
  score := (prefixSurvivalSet stayFalseSpec 1).indicator (fun _ => (1 : ℝ))
  measurable_score :=
    measurable_const.indicator (measurableSet_prefixSurvivalSet stayFalseSpec 1)
  score_nonneg := by
    intro w
    by_cases hw : w ∈ prefixSurvivalSet stayFalseSpec 1 <;>
      simp [Set.indicator, hw]
  score_le_one := by
    intro w
    by_cases hw : w ∈ prefixSurvivalSet stayFalseSpec 1 <;>
      simp [Set.indicator, hw]

/-- A bounded measurable prefix indicator integrates exactly to the already
defined one-step finite survival probability. -/
theorem finiteSurvivalScore_eq_survival
    (M : StrategicWorldModel Bool Bool Bool) (y : JointState Bool Bool) :
    finiteSurvivalScore.fromKernel 1 M.inducedKernel y =
      (survivalProbability M stayFalseSpec y 1).toReal := by
  rw [survivalProbability_toReal_eq_prefix]
  change
    (∫ w, (prefixSurvivalSet stayFalseSpec 1).indicator
      (fun _ => (1 : ℝ)) w
      ∂(ProbabilitySupport.finitePrefixLaw M.inducedKernel y 1)) =
      (ProbabilitySupport.finitePrefixLaw M.inducedKernel y 1).real
        (prefixSurvivalSet stayFalseSpec 1)
  exact integral_indicator_one (measurableSet_prefixSurvivalSet stayFalseSpec 1)

/-- The finite property is baseline-one at every original comparison state. -/
theorem baselineScore_one (y : JointState Bool Bool)
    (hy : y ∈ comparisonStay.states) :
    baselinePropertyValue (finiteSurvivalScore.toRegimeProperty 1) modelB y = 1 := by
  have hregion : y ∈ stayFalseSpec.region :=
    comparisonStay.states_subset_region hy
  rw [← finitePathExpectation_eq_baselineProperty modelB y 1 finiteSurvivalScore,
    finiteSurvivalScore_eq_survival, modelB_survival_one hregion]
  simp

/-- The same finite property becomes zero under the typed strategic
intervention; no intervened persistence assumption is made. -/
theorem interventionScore_zero (y : JointState Bool Bool)
    (hy : y ∈ comparisonStay.states) :
    intervenedPropertyValue (finiteSurvivalScore.toRegimeProperty 1)
      interventionB.intervention y = 0 := by
  have hregion : y ∈ stayFalseSpec.region :=
    comparisonStay.states_subset_region hy
  rw [← finitePathExpectation_eq_intervenedProperty interventionB y 1 finiteSurvivalScore,
    finiteSurvivalScore_eq_survival, interventionB_survival_zero hregion]
  simp

/-- A genuine positive finite constitutive effect, uniformly equal to one. -/
theorem uniformMargin_ge_one :
    (1 : ℝ) ≤ constitutiveMargin modelB stayFalseSpec familyB
      (finiteSurvivalScore.toRegimeProperty 1) comparisonStay interventionB := by
  unfold constitutiveMargin
  apply le_csInf
  · rcases comparisonStay.states_nonempty with ⟨y, hy⟩
    exact ⟨constitutiveEffect modelB
      (finiteSurvivalScore.toRegimeProperty 1) interventionB y, ⟨y, hy, rfl⟩⟩
  · intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    unfold constitutiveEffect
    rw [baselineScore_one y hy, interventionScore_zero y hy]
    norm_num [Real.dist_eq]

/-- A nontrivial CQ-1 certificate: uniform baseline survival and one full
unit of constitutive margin; not an Exact GR/PR claim. -/
theorem positiveFiniteCertificate :
    FiniteConstitutiveCertificate modelB stayFalseSpec familyB
      comparisonStay interventionB 1 finiteSurvivalScore 0 1 := by
  refine ⟨?_, by norm_num, uniformMargin_ge_one⟩
  refine ⟨by norm_num, ?_⟩
  intro y hy
  rw [modelB_survival_one hy]
  simp

/-- The control edge case: a shared point-started zero-transition score cannot
be constitutively sensitive to any intervention-induced transition kernel. -/
theorem zeroHorizon_no_kernel_effect
    (y : JointState Bool Bool)
    (f : FinitePathProperty (JointState Bool Bool) 0) :
    f.fromKernel 0 modelB.inducedKernel y =
      f.fromKernel 0 interventionB.intervention.apply.inducedKernel y :=
  expected_zero_independent_of_kernel _ _ y f

end CertificateExamples
end ConstitutiveQuasi
end PermanssonResearch
