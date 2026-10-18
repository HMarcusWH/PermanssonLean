import PermanssonResearch.ConstitutiveQuasi.LocalizedPrefixError
import PermanssonResearch.ConstitutiveQuasi.CertificateExamples
import Mathlib.Tactic

/-!
A2-P02 semantic fixture using the frozen Bool × Bool strategic-world model
and its two-start comparison basin. The approximation is the SAME typed physical model on both sides.
The report perturbs the baseline 1 to 9/10 and treatment 0 to 1/10, so its
margin is 4/5. Each reporting error is 1/10; all model errors are zero.
This is an example of a *finite-prefix original-margin* certificate, not an
Exact GR/PR or an empirical statement.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

namespace PermanssonResearch.ConstitutiveQuasi.LocalizedExamples

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonLean.Section7ConstitutiveNoninvariance
open PermanssonLean.ProbabilitySupport
open PermanssonResearch.ConstitutiveQuasi.CertificateExamples
open PermanssonResearch.Probability
open PermanssonResearch.Perturbation

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable def reportingProfile : PerturbedPropertyProfile (JointState Bool Bool) ℝ where
  baseline := fun _ => 9 / 10
  intervention := fun _ => 1 / 10

/-- The existing matched-pair interface, with component AND target equality. -/
noncomputable def matchedPair : PrimitiveModelPair modelB familyB interventionB where
  approximate := modelB
  approximateFamily := familyB
  approximateIntervention := interventionB
  component_eq := rfl
  target_eq := rfl

noncomputable def exactLocalizedErrors :
    LocalizedProtocolErrors modelB stayFalseSpec familyB comparisonStay
      interventionB matchedPair 1 finiteSurvivalScore reportingProfile where
  baseGood := fun _ => Set.univ
  treatedGood := fun _ => Set.univ
  baseGood_measurable := fun _ => MeasurableSet.univ
  treatedGood_measurable := fun _ => MeasurableSet.univ
  baseEta := fun _ => 0
  baseBadVisit := fun _ => 0
  treatedEta := fun _ => 0
  treatedBadVisit := fun _ => 0
  baseEta_nonneg := by intro; norm_num
  baseEta_le_one := by intro; norm_num
  baseBadVisit_nonneg := by intro; norm_num
  treatedEta_nonneg := by intro; norm_num
  treatedEta_le_one := by intro; norm_num
  treatedBadVisit_nonneg := by intro; norm_num
  base_good_row := by
    intro n w hw
    change eventTotalVariation (modelB.inducedKernel _) (modelB.inducedKernel _) ≤ 0
    exact le_of_eq (eventTotalVariation_self _)
  treated_good_row := by
    intro n w hw
    change eventTotalVariation
      (interventionB.intervention.apply.inducedKernel _)
      (interventionB.intervention.apply.inducedKernel _) ≤ 0
    exact le_of_eq (eventTotalVariation_self _)
  base_bad_visit := by
    intro y hy n
    simp
  treated_bad_visit := by
    intro y hy n
    simp
  approxBaseInitial := fun y => ⟨Measure.dirac y, inferInstance⟩
  approxTreatedInitial := fun y => ⟨Measure.dirac y, inferInstance⟩
  initialBaseError := 0
  initialTreatedError := 0
  initialBaseError_nonneg := by norm_num
  initialTreatedError_nonneg := by norm_num
  initialBase_error := by
    intro y hy
    exact le_of_eq (eventTotalVariation_self _)
  initialTreated_error := by
    intro y hy
    exact le_of_eq (eventTotalVariation_self _)
  reportBase := 1 / 10
  reportTreated := 1 / 10
  reportBase_nonneg := by norm_num
  reportTreated_nonneg := by norm_num
  reportBase_error := by
    intro y hy
    have hvalue : finiteSurvivalScore.fromKernel 1 modelB.inducedKernel y = 1 :=
      (finitePathExpectation_eq_baselineProperty modelB y 1 finiteSurvivalScore).trans
        (baselineScore_one y hy)
    change dist (finiteSurvivalScore.expected 1
      (mixedFinitePrefixLaw modelB.inducedKernel (Measure.dirac y) 1))
      (9 / 10 : ℝ) ≤ 1 / 10
    rw [mixedFinitePrefixLaw_dirac]
    change dist (finiteSurvivalScore.fromKernel 1 modelB.inducedKernel y)
      (9 / 10 : ℝ) ≤ 1 / 10
    rw [hvalue]
    norm_num [Real.dist_eq]
  reportTreated_error := by
    intro y hy
    have hvalue : finiteSurvivalScore.fromKernel 1
        interventionB.intervention.apply.inducedKernel y = 0 :=
      (finitePathExpectation_eq_intervenedProperty interventionB y 1 finiteSurvivalScore).trans
        (interventionScore_zero y hy)
    change dist (finiteSurvivalScore.expected 1 (mixedFinitePrefixLaw
      interventionB.intervention.apply.inducedKernel (Measure.dirac y) 1))
      (1 / 10 : ℝ) ≤ 1 / 10
    rw [mixedFinitePrefixLaw_dirac]
    change dist (finiteSurvivalScore.fromKernel 1
      interventionB.intervention.apply.inducedKernel y) (1 / 10 : ℝ) ≤ 1 / 10
    rw [hvalue]
    norm_num [Real.dist_eq]

/-- The profile's measured effect is 4/5 at every original comparison start. -/
theorem reportedEffect_four_fifths (y : JointState Bool Bool) :
    perturbedConstitutiveEffect reportingProfile y = 4 / 5 := by
  norm_num [perturbedConstitutiveEffect, reportingProfile, Real.dist_eq]

/-- We take the infimum over the entire ORIGINAL nonempty comparison set. -/
theorem reportedMargin_four_fifths :
    perturbedConstitutiveMargin modelB stayFalseSpec comparisonStay reportingProfile =
      4 / 5 := by
  have hset : perturbedConstitutiveEffect reportingProfile '' comparisonStay.states =
      {(4 / 5 : ℝ)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp [reportedEffect_four_fifths]
    · intro hx
      obtain ⟨y, hy⟩ := comparisonStay.states_nonempty
      have hx' : x = (4 / 5 : ℝ) := (Set.mem_singleton_iff).mp hx
      exact ⟨y, hy, (reportedEffect_four_fifths y).trans hx'.symm⟩
  simp [perturbedConstitutiveMargin, hset]

/-- Explicit zero model budget, with both nonzero reporting errors retained. -/
theorem localizedBudget_total_one_fifth :
    (exactLocalizedErrors.baselineBudget + exactLocalizedErrors.reportBase) +
      (exactLocalizedErrors.interventionBudget + exactLocalizedErrors.reportTreated) =
      1 / 5 := by
  norm_num [LocalizedProtocolErrors.baselineBudget,
    LocalizedProtocolErrors.interventionBudget, exactLocalizedErrors]

/-- The original uniform margin is certified positive from the report. -/
theorem originalMargin_ge_three_fifths :
    (3 / 5 : ℝ) ≤ constitutiveMargin modelB stayFalseSpec familyB
      (finiteSurvivalScore.toRegimeProperty 1) comparisonStay interventionB := by
  have hbound := exactLocalizedErrors.reportedMargin_abs_le
  rw [reportedMargin_four_fifths] at hbound
  rw [localizedBudget_total_one_fifth] at hbound
  have hleft := (abs_le.mp hbound).2
  linarith

/-- The same certificate has the positive-margin implication. -/
theorem originalMargin_positive :
    0 < constitutiveMargin modelB stayFalseSpec familyB
      (finiteSurvivalScore.toRegimeProperty 1) comparisonStay interventionB := by
  linarith [originalMargin_ge_three_fifths]

/-- An attempt to pretend the baseline reporting error is zero fails. -/
theorem cannot_omit_baseline_report_error :
    ¬ dist (1 : ℝ) (9 / 10) ≤ 0 := by
  norm_num [Real.dist_eq]

/-- An attempt to pretend the treatment reporting error is zero fails. -/
theorem cannot_omit_treatment_report_error :
    ¬ dist (0 : ℝ) (1 / 10) ≤ 0 := by
  norm_num [Real.dist_eq]

/-- A score that deliberately observes time zero; a changed initial law is
not made invisible by setting the transition horizon to zero. -/
noncomputable def initialScore : FinitePathProperty Bool 0 where
  score := fun w => if w ⟨0, Finset.mem_Iic.mpr le_rfl⟩ then 1 else 0
  measurable_score := measurable_of_finite _
  score_nonneg := by intro w; split <;> norm_num
  score_le_one := by intro w; split <;> norm_num

theorem initialScore_point (b : Bool) :
    initialScore.fromKernel 0 (Kernel.id : Kernel Bool Bool) b =
      if b then 1 else 0 := by
  simp only [FinitePathProperty.fromKernel, FinitePathProperty.expected,
    finitePrefixLaw, initialScore]
  rw [Kernel.id_apply, integral_dirac]
  rfl

/-- Both laws are valid probability laws of the same actual trajectory kernel;
only the initial state changes. This is the compiler mutant's positive control. -/
theorem initialMismatch_gap_one :
    |initialScore.fromKernel 0 (Kernel.id : Kernel Bool Bool) false -
      initialScore.expected 0
        (mixedFinitePrefixLaw (Kernel.id : Kernel Bool Bool) (Measure.dirac true) 0)| = 1 := by
  rw [mixedFinitePrefixLaw_dirac]
  change |initialScore.fromKernel 0 (Kernel.id : Kernel Bool Bool) false -
    initialScore.fromKernel 0 (Kernel.id : Kernel Bool Bool) true| = 1
  rw [initialScore_point false, initialScore_point true]
  norm_num

end PermanssonResearch.ConstitutiveQuasi.LocalizedExamples

