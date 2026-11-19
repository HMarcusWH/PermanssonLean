import PermanssonResearch.ConstitutiveQuasi.LocalizedPrefixExamples
import PermanssonResearch.StrategicWorld.DeterministicOrbit

/-!
# Original Q-04: intervention reaches a baseline-unvisited defective row

The true model, its action intervention, and both original comparison starts
are the frozen Bool × Bool source fixture. The approximate world below agrees
with every baseline row. Under the matched action intervention it agrees at
physical false, but disagrees maximally at physical true. From either original
comparison start the baseline never reaches that state; the true intervention
reaches it at time one. The resulting two-transition output gap is one.

This is a finite actual-kernel/prefix-law certificate. Each strategic
intervention preserves its own world's primitive; the approximation compares
different worlds and is not itself called a strategic intervention.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

namespace PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonLean.Section7ConstitutiveNoninvariance
open PermanssonLean.ProbabilitySupport
open PermanssonResearch.ConstitutiveQuasi.CertificateExamples
open PermanssonResearch.Probability PermanssonResearch.Perturbation
open PermanssonResearch.StrategicWorld

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable def approximateWorld : Kernel (WorldInput Bool Bool Bool) Bool :=
  Kernel.deterministic (fun z => if z.2 then z.1.2 else !z.1.2)
    (by exact Measurable.of_discrete)

noncomputable def approximateModel : StrategicWorldModel Bool Bool Bool where
  generator := generatorB
  world := approximateWorld
  world_isMarkov := by unfold approximateWorld; infer_instance

def approximateFamily : InterventionFamily approximateModel Unit where
  targetOf _ := .actionSelection
  admissible _ _ := True

noncomputable def approximateTypedIntervention : TypedIntervention approximateFamily where
  component := ()
  replacement := falseReplacement

noncomputable def approximateIntervention :
    AdmissibleStrategicIntervention approximateFamily where
  intervention := approximateTypedIntervention
  accepted := by trivial
  strategic := by change True; trivial

/-- Assemble the dependent record with explicit model/family parameters before
instantiating the concrete finite world. -/
noncomputable def assembleMatchedPair
    (M : StrategicWorldModel Bool Bool Bool) (F : InterventionFamily M Unit)
    (J : AdmissibleStrategicIntervention F)
    (hc : J.intervention.component = interventionB.intervention.component)
    (ht : F.targetOf J.intervention.component = familyB.targetOf interventionB.intervention.component) :
    PrimitiveModelPair modelB familyB interventionB where
  approximate := M
  approximateFamily := F
  approximateIntervention := J
  component_eq := hc
  target_eq := ht

theorem matched_targets (a b : Unit) :
    approximateFamily.targetOf a = familyB.targetOf b := rfl

noncomputable def matchedPair : PrimitiveModelPair modelB familyB interventionB :=
  assembleMatchedPair approximateModel approximateFamily approximateIntervention
    (Subsingleton.elim _ _) (matched_targets _ _)

theorem matched_intervention_worlds_fixed :
    interventionB.intervention.apply.world = modelB.world ∧
    approximateIntervention.intervention.apply.world = approximateModel.world :=
  ⟨matchedPair.original_world_fixed, matchedPair.approximate_world_fixed⟩

theorem baseline_row (y : JointState Bool Bool) :
    modelB.inducedKernel y = Measure.dirac y := by
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply modelB y hE]
  rcases y with ⟨s, x⟩
  cases s <;> cases x <;>
    simp [modelB, generatorB, actionTrue, updatePreserve, worldB,
      Kernel.deterministic_apply, Set.indicator] <;>
    rfl

theorem approximate_baseline_row (y : JointState Bool Bool) :
    approximateModel.inducedKernel y = Measure.dirac y := by
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply approximateModel y hE]
  rcases y with ⟨s, x⟩
  cases s <;> cases x <;>
    simp [approximateModel, generatorB, actionTrue, updatePreserve,
      approximateWorld, Kernel.deterministic_apply, Set.indicator] <;>
    rfl

def trueStep (y : JointState Bool Bool) : JointState Bool Bool := (y.1, true)
def approximateStep (y : JointState Bool Bool) : JointState Bool Bool := (y.1, !y.2)

theorem treated_row (y : JointState Bool Bool) :
    interventionB.intervention.apply.inducedKernel y = Measure.dirac (trueStep y) := by
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply interventionB.intervention.apply y hE]
  rcases y with ⟨s, x⟩
  cases s <;> cases x <;>
    simp [interventionB, typedInterventionB, familyB, falseReplacement,
      TypedIntervention.apply, applyReplacement, modelB, generatorB, actionFalse, updatePreserve,
      worldB, Kernel.deterministic_apply, trueStep, Set.indicator] <;>
    rfl

theorem approximate_treated_row (y : JointState Bool Bool) :
    approximateIntervention.intervention.apply.inducedKernel y =
      Measure.dirac (approximateStep y) := by
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply approximateIntervention.intervention.apply y hE]
  rcases y with ⟨s, x⟩
  cases s <;> cases x <;>
    simp [approximateIntervention, approximateTypedIntervention, approximateFamily,
      falseReplacement, TypedIntervention.apply, applyReplacement, approximateModel, generatorB,
      actionFalse, updatePreserve, approximateWorld, Kernel.deterministic_apply,
      approximateStep, Set.indicator] <;>
    rfl

theorem baseline_rows_agree (y : JointState Bool Bool) :
    modelB.inducedKernel y = approximateModel.inducedKernel y := by
  rw [baseline_row, approximate_baseline_row]

theorem treated_good_rows_agree (y : JointState Bool Bool) (hy : y.2 = false) :
    interventionB.intervention.apply.inducedKernel y =
      approximateIntervention.intervention.apply.inducedKernel y := by
  rw [treated_row, approximate_treated_row]
  simp [trueStep, approximateStep, hy]

theorem treated_bad_row_defect_one (s : Bool) :
    eventTotalVariation (interventionB.intervention.apply.inducedKernel (s, true))
      (approximateIntervention.intervention.apply.inducedKernel (s, true)) = 1 := by
  rw [treated_row, approximate_treated_row]
  simp only [trueStep, approximateStep, Bool.not_true]
  apply le_antisymm (eventTotalVariation_le_one _ _)
  have h := abs_measureReal_sub_le_eventTotalVariation
    (Measure.dirac (s, true)) (Measure.dirac (s, false))
    (s := {y : JointState Bool Bool | y.2 = true}) (by exact MeasurableSet.of_discrete)
  simpa [Measure.real, Measure.dirac_apply', Set.indicator] using h

/-- Reuse the canonical infinite-to-finite prefix theorem and deterministic
path theorem; this does not posit an independent finite process. -/
theorem deterministic_prefix
    (M : StrategicWorldModel Bool Bool Bool)
    (f : JointState Bool Bool → JointState Bool Bool)
    (hrow : ∀ y, M.inducedKernel y = Measure.dirac (f y))
    (y : JointState Bool Bool) (T : ℕ) :
    finitePrefixLaw M.inducedKernel y T =
      Measure.dirac (fun i : Finset.Iic T => detOrbit f y i) := by
  rw [← pathLaw_finitePrefix_eq M y T, pathLaw_dirac_of_deterministic M f hrow y,
    Measure.map_dirac' (Preorder.measurable_frestrictLe T)]
  rfl

theorem trueStep_iterate_succ (n : ℕ) (y : JointState Bool Bool) :
    trueStep^[n + 1] y = (y.1, true) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

def goodHistory (n : ℕ) : Set ((i : Finset.Iic n) → JointState Bool Bool) :=
  {w | (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 = false}

theorem goodHistory_measurable (n : ℕ) : MeasurableSet (goodHistory n) := by
  exact MeasurableSet.of_discrete

theorem baseline_bad_visit_zero (s : Bool) (n : ℕ) :
    finitePrefixLaw modelB.inducedKernel (s, false) n (goodHistory n)ᶜ = 0 := by
  rw [deterministic_prefix modelB id (by simpa using baseline_row) (s, false) n]
  simp [goodHistory, detOrbit, Function.iterate_id]

theorem treated_bad_visit_schedule (s : Bool) (n : ℕ) :
    finitePrefixLaw interventionB.intervention.apply.inducedKernel (s, false) n
      (goodHistory n)ᶜ = if n = 0 then 0 else 1 := by
  rw [deterministic_prefix _ trueStep treated_row (s, false) n]
  cases n with
  | zero => simp [goodHistory, detOrbit]
  | succ n => simp [goodHistory, detOrbit, trueStep_iterate_succ]

theorem treated_bad_visit_one (s : Bool) :
    finitePrefixLaw interventionB.intervention.apply.inducedKernel (s, false) 1
      (goodHistory 1)ᶜ = 1 := by
  rw [treated_bad_visit_schedule]
  norm_num

noncomputable def terminalTrueScore : FinitePathProperty (JointState Bool Bool) 2 where
  score := fun w => if (w ⟨2, Finset.mem_Iic.mpr le_rfl⟩).2 then 1 else 0
  measurable_score := measurable_of_finite _
  score_nonneg := by intro w; split <;> norm_num
  score_le_one := by intro w; split <;> norm_num

theorem baseline_score_zero (s : Bool) :
    terminalTrueScore.fromKernel 2 modelB.inducedKernel (s, false) = 0 := by
  unfold FinitePathProperty.fromKernel FinitePathProperty.expected
  rw [deterministic_prefix modelB id (by simpa using baseline_row)]
  simp [terminalTrueScore, detOrbit, Function.iterate_id]

theorem approximate_baseline_score_zero (s : Bool) :
    terminalTrueScore.fromKernel 2 approximateModel.inducedKernel (s, false) = 0 := by
  unfold FinitePathProperty.fromKernel FinitePathProperty.expected
  rw [deterministic_prefix approximateModel id (by simpa using approximate_baseline_row)]
  simp [terminalTrueScore, detOrbit, Function.iterate_id]

theorem treated_score_one (s : Bool) :
    terminalTrueScore.fromKernel 2 interventionB.intervention.apply.inducedKernel
      (s, false) = 1 := by
  unfold FinitePathProperty.fromKernel FinitePathProperty.expected
  rw [deterministic_prefix _ trueStep treated_row]
  simp [terminalTrueScore, detOrbit, trueStep_iterate_succ]

theorem approximate_treated_score_zero (s : Bool) :
    terminalTrueScore.fromKernel 2 approximateIntervention.intervention.apply.inducedKernel
      (s, false) = 0 := by
  unfold FinitePathProperty.fromKernel FinitePathProperty.expected
  rw [deterministic_prefix _ approximateStep approximate_treated_row]
  simp [terminalTrueScore, detOrbit, Function.iterate_succ_apply', approximateStep]

theorem actual_treated_output_gap_one (s : Bool) :
    |terminalTrueScore.fromKernel 2 interventionB.intervention.apply.inducedKernel (s, false) -
      terminalTrueScore.fromKernel 2 approximateIntervention.intervention.apply.inducedKernel
        (s, false)| = 1 := by
  rw [treated_score_one, approximate_treated_score_zero]
  norm_num

def treatedVisitBudget (n : ℕ) : ℝ := if n = 0 then 0 else 1

/-- Exact approximate-model outputs, with no numerical/reporting error. -/
noncomputable def report : PerturbedPropertyProfile (JointState Bool Bool) ℝ where
  baseline y := terminalTrueScore.fromKernel 2 approximateModel.inducedKernel y
  intervention y := terminalTrueScore.fromKernel 2
    approximateIntervention.intervention.apply.inducedKernel y

/-- The genuine baseline and intervention each supply their own bad visits.
The full original comparison set is retained, and both initial laws match. -/
noncomputable def localizedErrors :
    LocalizedProtocolErrors modelB stayFalseSpec familyB comparisonStay
      interventionB matchedPair 2 terminalTrueScore report where
  baseGood := goodHistory
  treatedGood := goodHistory
  baseGood_measurable := goodHistory_measurable
  treatedGood_measurable := goodHistory_measurable
  baseEta _ := 0
  baseBadVisit _ := 0
  treatedEta _ := 0
  treatedBadVisit := treatedVisitBudget
  baseEta_nonneg := by intro; norm_num
  baseEta_le_one := by intro; norm_num
  baseBadVisit_nonneg := by intro; norm_num
  treatedEta_nonneg := by intro; norm_num
  treatedEta_le_one := by intro; norm_num
  treatedBadVisit_nonneg := by intro n; unfold treatedVisitBudget; split <;> norm_num
  base_good_row := by
    intro n w _
    change eventTotalVariation (modelB.inducedKernel _)
      (approximateModel.inducedKernel _) ≤ 0
    rw [baseline_rows_agree]
    exact le_of_eq (eventTotalVariation_self _)
  treated_good_row := by
    intro n w hw
    change (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 = false at hw
    change eventTotalVariation (interventionB.intervention.apply.inducedKernel _)
      (approximateIntervention.intervention.apply.inducedKernel _) ≤ 0
    rw [treated_good_rows_agree _ hw]
    exact le_of_eq (eventTotalVariation_self _)
  base_bad_visit := by
    intro y hy n
    have hx : y.2 = false := hy
    rcases y with ⟨s, x⟩
    dsimp at hx
    subst x
    rw [baseline_bad_visit_zero]
    simp
  treated_bad_visit := by
    intro y hy n
    have hx : y.2 = false := hy
    rcases y with ⟨s, x⟩
    dsimp at hx
    subst x
    rw [treated_bad_visit_schedule]
    simp only [treatedVisitBudget]
    split_ifs <;> simp
  approxBaseInitial y := ⟨Measure.dirac y, inferInstance⟩
  approxTreatedInitial y := ⟨Measure.dirac y, inferInstance⟩
  initialBaseError := 0
  initialTreatedError := 0
  initialBaseError_nonneg := by norm_num
  initialTreatedError_nonneg := by norm_num
  initialBase_error := by intro y _; exact le_of_eq (eventTotalVariation_self _)
  initialTreated_error := by intro y _; exact le_of_eq (eventTotalVariation_self _)
  reportBase := 0
  reportTreated := 0
  reportBase_nonneg := by norm_num
  reportTreated_nonneg := by norm_num
  reportBase_error := by
    intro y _
    change dist (terminalTrueScore.expected 2
      (mixedFinitePrefixLaw approximateModel.inducedKernel (Measure.dirac y) 2))
      (terminalTrueScore.fromKernel 2 approximateModel.inducedKernel y) ≤ 0
    rw [mixedFinitePrefixLaw_dirac]
    exact le_of_eq (dist_self _)
  reportTreated_error := by
    intro y _
    change dist (terminalTrueScore.expected 2
      (mixedFinitePrefixLaw approximateIntervention.intervention.apply.inducedKernel
        (Measure.dirac y) 2))
      (terminalTrueScore.fromKernel 2
        approximateIntervention.intervention.apply.inducedKernel y) ≤ 0
    rw [mixedFinitePrefixLaw_dirac]
    exact le_of_eq (dist_self _)

theorem baseline_budget_zero : localizedErrors.baselineBudget = 0 := by
  norm_num [LocalizedProtocolErrors.baselineBudget, localizedErrors]

theorem intervention_budget_one : localizedErrors.interventionBudget = 1 := by
  norm_num [LocalizedProtocolErrors.interventionBudget, localizedErrors,
    treatedVisitBudget, Finset.sum_range_succ]

theorem actual_output_error_is_budgeted (s : Bool) :
    |terminalTrueScore.fromKernel 2 interventionB.intervention.apply.inducedKernel (s, false) -
      terminalTrueScore.fromKernel 2 approximateIntervention.intervention.apply.inducedKernel
        (s, false)| ≤ localizedErrors.interventionBudget := by
  rw [actual_treated_output_gap_one, intervention_budget_one]

theorem baseline_budget_cannot_pay_intervention_error (s : Bool) :
    ¬ |terminalTrueScore.fromKernel 2 interventionB.intervention.apply.inducedKernel (s, false) -
      terminalTrueScore.fromKernel 2 approximateIntervention.intervention.apply.inducedKernel
        (s, false)| ≤ localizedErrors.baselineBudget := by
  rw [actual_treated_output_gap_one, baseline_budget_zero]
  norm_num

theorem original_effect_one (y : JointState Bool Bool) (hy : y ∈ comparisonStay.states) :
    constitutiveEffect modelB (terminalTrueScore.toRegimeProperty 2) interventionB y = 1 := by
  have hx : y.2 = false := hy
  rcases y with ⟨s, x⟩
  dsimp at hx
  subst x
  unfold constitutiveEffect
  rw [← finitePathExpectation_eq_baselineProperty,
    ← finitePathExpectation_eq_intervenedProperty, baseline_score_zero, treated_score_one]
  norm_num [Real.dist_eq]

theorem reported_effect_zero (y : JointState Bool Bool) (hy : y ∈ comparisonStay.states) :
    perturbedConstitutiveEffect report y = 0 := by
  have hx : y.2 = false := hy
  rcases y with ⟨s, x⟩
  dsimp at hx
  subst x
  change dist (terminalTrueScore.fromKernel 2 approximateModel.inducedKernel (s, false))
    (terminalTrueScore.fromKernel 2
      approximateIntervention.intervention.apply.inducedKernel (s, false)) = 0
  rw [approximate_baseline_score_zero, approximate_treated_score_zero]
  exact dist_self _

theorem original_margin_one :
    constitutiveMargin modelB stayFalseSpec familyB
      (terminalTrueScore.toRegimeProperty 2) comparisonStay interventionB = 1 := by
  have hs : constitutiveEffect modelB (terminalTrueScore.toRegimeProperty 2) interventionB ''
      comparisonStay.states = {(1 : ℝ)} := by
    ext r
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using original_effect_one y hy
    · intro hr
      obtain ⟨y, hy⟩ := comparisonStay.states_nonempty
      have hr' : r = (1 : ℝ) := Set.mem_singleton_iff.mp hr
      exact ⟨y, hy, (original_effect_one y hy).trans hr'.symm⟩
  simp [constitutiveMargin, hs]

theorem reported_margin_zero :
    perturbedConstitutiveMargin modelB stayFalseSpec comparisonStay report = 0 := by
  have hs : perturbedConstitutiveEffect report '' comparisonStay.states = {(0 : ℝ)} := by
    ext r
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using reported_effect_zero y hy
    · intro hr
      obtain ⟨y, hy⟩ := comparisonStay.states_nonempty
      have hr' : r = (0 : ℝ) := Set.mem_singleton_iff.mp hr
      exact ⟨y, hy, (reported_effect_zero y hy).trans hr'.symm⟩
  simp [perturbedConstitutiveMargin, hs]

/-- The original-margin error is exactly the charged intervention budget;
baseline, initial-law, and numerical/reporting errors contribute zero. -/
theorem original_margin_error_equals_charged_budget :
    |perturbedConstitutiveMargin modelB stayFalseSpec comparisonStay report -
      constitutiveMargin modelB stayFalseSpec familyB
        (terminalTrueScore.toRegimeProperty 2) comparisonStay interventionB| =
      localizedErrors.baselineBudget + localizedErrors.interventionBudget := by
  rw [reported_margin_zero, original_margin_one, baseline_budget_zero, intervention_budget_one]
  norm_num

theorem original_margin_error_certificate :
    |perturbedConstitutiveMargin modelB stayFalseSpec comparisonStay report -
      constitutiveMargin modelB stayFalseSpec familyB
        (terminalTrueScore.toRegimeProperty 2) comparisonStay interventionB| ≤ 1 := by
  have h := localizedErrors.reportedMargin_abs_le
  simpa only [baseline_budget_zero, intervention_budget_one,
    show localizedErrors.reportBase = 0 from rfl,
    show localizedErrors.reportTreated = 0 from rfl, add_zero, zero_add] using h

end PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum

-- Frozen original model, canonical laws, and separate two-sided error providers.
#check PermanssonLean.Section7ConstitutiveNoninvariance.modelB
#print axioms PermanssonLean.Section7ConstitutiveNoninvariance.modelB
#check PermanssonLean.Section7ConstitutiveNoninvariance.familyB
#print axioms PermanssonLean.Section7ConstitutiveNoninvariance.familyB
#check PermanssonLean.Section7ConstitutiveNoninvariance.interventionB
#print axioms PermanssonLean.Section7ConstitutiveNoninvariance.interventionB
#check PermanssonResearch.ConstitutiveQuasi.CertificateExamples.comparisonStay
#print axioms PermanssonResearch.ConstitutiveQuasi.CertificateExamples.comparisonStay
#check PermanssonResearch.Perturbation.PrimitiveModelPair
#print axioms PermanssonResearch.Perturbation.PrimitiveModelPair
#check PermanssonResearch.Perturbation.PrimitiveModelPair.original_world_fixed
#print axioms PermanssonResearch.Perturbation.PrimitiveModelPair.original_world_fixed
#check PermanssonResearch.Perturbation.PrimitiveModelPair.approximate_world_fixed
#print axioms PermanssonResearch.Perturbation.PrimitiveModelPair.approximate_world_fixed
#check PermanssonResearch.ConstitutiveQuasi.pathLaw_finitePrefix_eq
#print axioms PermanssonResearch.ConstitutiveQuasi.pathLaw_finitePrefix_eq
#check PermanssonResearch.StrategicWorld.pathLaw_dirac_of_deterministic
#print axioms PermanssonResearch.StrategicWorld.pathLaw_dirac_of_deterministic
#check PermanssonLean.ProbabilitySupport.finitePrefixLaw
#print axioms PermanssonLean.ProbabilitySupport.finitePrefixLaw
#check PermanssonLean.ProbabilitySupport.eventTotalVariation
#print axioms PermanssonLean.ProbabilitySupport.eventTotalVariation
#check PermanssonResearch.Probability.finitePrefixLaw_tv_le_goodVisits
#print axioms PermanssonResearch.Probability.finitePrefixLaw_tv_le_goodVisits
#check PermanssonResearch.Probability.finitePathExpectation_abs_le_goodVisits_initial
#print axioms PermanssonResearch.Probability.finitePathExpectation_abs_le_goodVisits_initial
#check PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors
#print axioms PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors
#check PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors.baselineBudget
#print axioms PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors.baselineBudget
#check PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors.interventionBudget
#print axioms PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors.interventionBudget
#check PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors.toConstitutiveOutputErrors
#print axioms PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors.toConstitutiveOutputErrors
#check PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors.reportedMargin_abs_le
#print axioms PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors.reportedMargin_abs_le
#check PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors.trueMargin_pos_of_reported
#print axioms PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors.trueMargin_pos_of_reported
#check PermanssonResearch.ConstitutiveQuasi.LocalizedExamples.exactLocalizedErrors
#print axioms PermanssonResearch.ConstitutiveQuasi.LocalizedExamples.exactLocalizedErrors
#check PermanssonResearch.ConstitutiveQuasi.LocalizedExamples.cannot_omit_treatment_report_error
#print axioms PermanssonResearch.ConstitutiveQuasi.LocalizedExamples.cannot_omit_treatment_report_error

-- Complete actual-intervention visit, kernel, score, and original-margin fixture.
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximateWorld
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximateWorld
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximateModel
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximateModel
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximateFamily
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximateFamily
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximateTypedIntervention
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximateTypedIntervention
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximateIntervention
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximateIntervention
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.assembleMatchedPair
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.assembleMatchedPair
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.matched_targets
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.matched_targets
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.matchedPair
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.matchedPair
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.matched_intervention_worlds_fixed
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.matched_intervention_worlds_fixed
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.baseline_row
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.baseline_row
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximate_baseline_row
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximate_baseline_row
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.trueStep
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.trueStep
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximateStep
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximateStep
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treated_row
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treated_row
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximate_treated_row
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximate_treated_row
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.baseline_rows_agree
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.baseline_rows_agree
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treated_good_rows_agree
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treated_good_rows_agree
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treated_bad_row_defect_one
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treated_bad_row_defect_one
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.deterministic_prefix
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.deterministic_prefix
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.trueStep_iterate_succ
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.trueStep_iterate_succ
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.goodHistory
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.goodHistory
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.goodHistory_measurable
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.goodHistory_measurable
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.baseline_bad_visit_zero
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.baseline_bad_visit_zero
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treated_bad_visit_schedule
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treated_bad_visit_schedule
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treated_bad_visit_one
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treated_bad_visit_one
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.terminalTrueScore
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.terminalTrueScore
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.baseline_score_zero
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.baseline_score_zero
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximate_baseline_score_zero
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximate_baseline_score_zero
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treated_score_one
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treated_score_one
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximate_treated_score_zero
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.approximate_treated_score_zero
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.actual_treated_output_gap_one
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.actual_treated_output_gap_one
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treatedVisitBudget
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.treatedVisitBudget
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.report
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.report
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.localizedErrors
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.localizedErrors
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.baseline_budget_zero
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.baseline_budget_zero
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.intervention_budget_one
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.intervention_budget_one
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.actual_output_error_is_budgeted
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.actual_output_error_is_budgeted
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.baseline_budget_cannot_pay_intervention_error
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.baseline_budget_cannot_pay_intervention_error
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.original_effect_one
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.original_effect_one
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.reported_effect_zero
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.reported_effect_zero
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.original_margin_one
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.original_margin_one
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.reported_margin_zero
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.reported_margin_zero
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.original_margin_error_equals_charged_budget
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.original_margin_error_equals_charged_budget
#check PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.original_margin_error_certificate
#print axioms PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum.original_margin_error_certificate
