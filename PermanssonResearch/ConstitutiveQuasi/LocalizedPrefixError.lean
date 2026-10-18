import PermanssonResearch.Probability.LocalizedFinitePrefix
import PermanssonResearch.ConstitutiveQuasi.PropertyErrors
import PermanssonResearch.Perturbation.PrimitiveModelPair
import Mathlib.Tactic

/-!
A2-P02 — localized, two-sided constitutive-margin transport.

1. Compare the *true* baseline kernel to its typed approximate baseline.
2. Compare the *true* intervened kernel to its typed approximate intervention.
3. Charge approximate initial-law mismatch independently on both sides.
4. Bound row defects by good-history and actual bad-visit probabilities,
   independently in both comparisons and UNIFORMLY over the frozen B₁.
5. Add independently verified numerical/reporting errors for each side.
6. Instantiate the ORIGINAL Proposition 5.2 output-error/margin interfaces.

The margin is not redefined. No Exact GR/PR, identified structural model, or
empirical predictive certificate is inferred from this finite-prefix result.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

namespace PermanssonResearch.ConstitutiveQuasi

open PermanssonLean.ProbabilitySupport
open PermanssonResearch.Probability
open PermanssonResearch.Perturbation

universe uS uX uA uH uC
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- The two schedules refer to DIFFERENT source laws. `baseBadVisit` is
computed under the genuine baseline; `treatedBadVisit` under the genuine
intervention. No baseline-reachability assumption replaces the latter. The pair type
also enforces the same named component and target constructor; each strategic
intervention keeps its own model's P. Cross-model P need not be equal. -/
structure LocalizedProtocolErrors
    (M : PermanssonLean.StrategicWorldModel S X A)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    {Component : Type uC}
    (F : PermanssonLean.InterventionFamily M Component)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec)
    (J : PermanssonLean.AdmissibleStrategicIntervention F)
    (pair : PrimitiveModelPair M F J)
    (T : ℕ) (f : FinitePathProperty (PermanssonLean.JointState S X) T)
    (report : PermanssonLean.RegimeSpecification.PerturbedPropertyProfile
      (PermanssonLean.JointState S X) ℝ) where
  baseGood : (n : ℕ) → Set ((i : Finset.Iic n) → PermanssonLean.JointState S X)
  treatedGood : (n : ℕ) → Set ((i : Finset.Iic n) → PermanssonLean.JointState S X)
  baseGood_measurable : ∀ n, MeasurableSet (baseGood n)
  treatedGood_measurable : ∀ n, MeasurableSet (treatedGood n)
  baseEta : ℕ → ℝ
  baseBadVisit : ℕ → ℝ
  treatedEta : ℕ → ℝ
  treatedBadVisit : ℕ → ℝ
  baseEta_nonneg : ∀ n, 0 ≤ baseEta n
  baseEta_le_one : ∀ n, baseEta n ≤ 1
  baseBadVisit_nonneg : ∀ n, 0 ≤ baseBadVisit n
  treatedEta_nonneg : ∀ n, 0 ≤ treatedEta n
  treatedEta_le_one : ∀ n, treatedEta n ≤ 1
  treatedBadVisit_nonneg : ∀ n, 0 ≤ treatedBadVisit n
  base_good_row : ∀ n w, w ∈ baseGood n →
    eventTotalVariation
      (M.inducedKernel (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
      (pair.approximate.inducedKernel (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) ≤ baseEta n
  treated_good_row : ∀ n w, w ∈ treatedGood n →
    eventTotalVariation
      (J.intervention.apply.inducedKernel (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
      (pair.approximateIntervention.intervention.apply.inducedKernel
        (w ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) ≤ treatedEta n
  base_bad_visit : ∀ y ∈ B₁.states, ∀ n,
    finitePrefixLaw M.inducedKernel y n (baseGood n)ᶜ ≤
      ENNReal.ofReal (baseBadVisit n)
  treated_bad_visit : ∀ y ∈ B₁.states, ∀ n,
    finitePrefixLaw J.intervention.apply.inducedKernel y n (treatedGood n)ᶜ ≤
      ENNReal.ofReal (treatedBadVisit n)
  approxBaseInitial : PermanssonLean.JointState S X →
    ProbabilityMeasure (PermanssonLean.JointState S X)
  approxTreatedInitial : PermanssonLean.JointState S X →
    ProbabilityMeasure (PermanssonLean.JointState S X)
  initialBaseError : ℝ
  initialTreatedError : ℝ
  initialBaseError_nonneg : 0 ≤ initialBaseError
  initialTreatedError_nonneg : 0 ≤ initialTreatedError
  initialBase_error : ∀ y ∈ B₁.states,
    eventTotalVariation (Measure.dirac y) (approxBaseInitial y) ≤ initialBaseError
  initialTreated_error : ∀ y ∈ B₁.states,
    eventTotalVariation (Measure.dirac y) (approxTreatedInitial y) ≤ initialTreatedError
  reportBase : ℝ
  reportTreated : ℝ
  reportBase_nonneg : 0 ≤ reportBase
  reportTreated_nonneg : 0 ≤ reportTreated
  reportBase_error : ∀ y ∈ B₁.states,
    dist (f.expected T (mixedFinitePrefixLaw pair.approximate.inducedKernel
      (approxBaseInitial y) T)) (report.baseline y) ≤ reportBase
  reportTreated_error : ∀ y ∈ B₁.states,
    dist (f.expected T (mixedFinitePrefixLaw
      pair.approximateIntervention.intervention.apply.inducedKernel
      (approxTreatedInitial y) T)) (report.intervention y) ≤ reportTreated

namespace LocalizedProtocolErrors

variable {M : PermanssonLean.StrategicWorldModel S X A}
  {spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H}
  {Component : Type uC} {F : PermanssonLean.InterventionFamily M Component}
  {B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec}
  {J : PermanssonLean.AdmissibleStrategicIntervention F}
  {pair : PrimitiveModelPair M F J}
  {T : ℕ} {f : FinitePathProperty (PermanssonLean.JointState S X) T}
  {report : PermanssonLean.RegimeSpecification.PerturbedPropertyProfile
    (PermanssonLean.JointState S X) ℝ}

/-- Actual finite-prefix source-law budget, with a separate approximate initial
law error. The true original comparison start and B₁ remain unchanged. -/
noncomputable def baselineBudget
    (h : LocalizedProtocolErrors M spec F B₁ J pair T f report) : ℝ :=
  min 1 (h.initialBaseError + ∑ n ∈ Finset.range T, (h.baseEta n + h.baseBadVisit n))

noncomputable def interventionBudget
    (h : LocalizedProtocolErrors M spec F B₁ J pair T f report) : ℝ :=
  min 1 (h.initialTreatedError + ∑ n ∈ Finset.range T, (h.treatedEta n + h.treatedBadVisit n))

lemma baselineBudget_nonneg
    (h : LocalizedProtocolErrors M spec F B₁ J pair T f report) :
    0 ≤ h.baselineBudget := by
  unfold baselineBudget
  refine le_min (by norm_num) (add_nonneg h.initialBaseError_nonneg ?_)
  exact Finset.sum_nonneg (fun n _ =>
    add_nonneg (h.baseEta_nonneg n) (h.baseBadVisit_nonneg n))

lemma interventionBudget_nonneg
    (h : LocalizedProtocolErrors M spec F B₁ J pair T f report) :
    0 ≤ h.interventionBudget := by
  unfold interventionBudget
  refine le_min (by norm_num) (add_nonneg h.initialTreatedError_nonneg ?_)
  exact Finset.sum_nonneg (fun n _ =>
    add_nonneg (h.treatedEta_nonneg n) (h.treatedBadVisit_nonneg n))

/-- Original output-error structure: genuinely derived model-law errors plus
independently bounded reporting errors, evaluated at every original B₁ start. -/
theorem toConstitutiveOutputErrors
    (h : LocalizedProtocolErrors M spec F B₁ J pair T f report) :
    PermanssonLean.RegimeSpecification.HasConstitutiveOutputErrors
      M spec F (f.toRegimeProperty T) B₁ J report
      (h.baselineBudget + h.reportBase)
      (h.interventionBudget + h.reportTreated) := by
  refine ⟨add_nonneg h.baselineBudget_nonneg h.reportBase_nonneg,
    add_nonneg h.interventionBudget_nonneg h.reportTreated_nonneg, ?_, ?_⟩
  · intro y hy
    have hb := finitePathExpectation_abs_le_goodVisits_initial
      M.inducedKernel pair.approximate.inducedKernel y (h.approxBaseInitial y) h.baseGood
      h.baseGood_measurable h.baseEta h.baseBadVisit
      h.baseEta_nonneg h.baseBadVisit_nonneg
      h.base_good_row (h.base_bad_visit y hy) (h.initialBase_error y hy) T f
    have hd :
        dist (PermanssonLean.RegimeSpecification.baselinePropertyValue
            (f.toRegimeProperty T) M y)
          (f.expected T (mixedFinitePrefixLaw pair.approximate.inducedKernel
            (h.approxBaseInitial y) T)) ≤ h.baselineBudget := by
      rw [← finitePathExpectation_eq_baselineProperty M y T f, Real.dist_eq]
      exact hb
    exact (dist_triangle _ _ _).trans
      (add_le_add hd (h.reportBase_error y hy))
  · intro y hy
    have hb := finitePathExpectation_abs_le_goodVisits_initial
      J.intervention.apply.inducedKernel
      pair.approximateIntervention.intervention.apply.inducedKernel y
      (h.approxTreatedInitial y) h.treatedGood
      h.treatedGood_measurable h.treatedEta h.treatedBadVisit
      h.treatedEta_nonneg h.treatedBadVisit_nonneg
      h.treated_good_row (h.treated_bad_visit y hy) (h.initialTreated_error y hy) T f
    have hd :
        dist (PermanssonLean.RegimeSpecification.intervenedPropertyValue
            (f.toRegimeProperty T) J.intervention y)
          (f.expected T (mixedFinitePrefixLaw
            pair.approximateIntervention.intervention.apply.inducedKernel
            (h.approxTreatedInitial y) T)) ≤ h.interventionBudget := by
      rw [← finitePathExpectation_eq_intervenedProperty J y T f, Real.dist_eq]
      exact hb
    exact (dist_triangle _ _ _).trans
      (add_le_add hd (h.reportTreated_error y hy))

/-- Q-LOCAL source implementation: two-sided ORIGINAL constitutive margin
error, with the true constitutive margin untouched. -/
theorem reportedMargin_abs_le
    (h : LocalizedProtocolErrors M spec F B₁ J pair T f report) :
    |PermanssonLean.RegimeSpecification.perturbedConstitutiveMargin
        M spec B₁ report -
      PermanssonLean.RegimeSpecification.constitutiveMargin
        M spec F (f.toRegimeProperty T) B₁ J| ≤
      (h.baselineBudget + h.reportBase) +
      (h.interventionBudget + h.reportTreated) := by
  exact PermanssonLean.RegimeSpecification.constitutiveMargin_perturbation_abs_le
    M spec F (f.toRegimeProperty T) B₁ J report
    (h.baselineBudget + h.reportBase)
    (h.interventionBudget + h.reportTreated) h.toConstitutiveOutputErrors

/-- A measured positive reported margin certifies a positive TRUE margin only
when both initial-law, both localized model, and both reporting errors are accounted for. -/
theorem trueMargin_pos_of_reported
    (h : LocalizedProtocolErrors M spec F B₁ J pair T f report)
    (hgap : (h.baselineBudget + h.reportBase) +
        (h.interventionBudget + h.reportTreated) <
      PermanssonLean.RegimeSpecification.perturbedConstitutiveMargin
        M spec B₁ report) :
    0 < PermanssonLean.RegimeSpecification.constitutiveMargin
      M spec F (f.toRegimeProperty T) B₁ J := by
  have habs := h.reportedMargin_abs_le
  have hl := (abs_le.mp habs).2
  linarith

/-- Conversely a known true margin robustly implies positive reported
separation; this does not certify the approximate model as an exact GR. -/
theorem reportedMargin_pos_of_true
    (h : LocalizedProtocolErrors M spec F B₁ J pair T f report)
    (hgap : (h.baselineBudget + h.reportBase) +
        (h.interventionBudget + h.reportTreated) <
      PermanssonLean.RegimeSpecification.constitutiveMargin
        M spec F (f.toRegimeProperty T) B₁ J) :
    0 < PermanssonLean.RegimeSpecification.perturbedConstitutiveMargin
      M spec B₁ report := by
  have habs := h.reportedMargin_abs_le
  have hr := (abs_le.mp habs).1
  linarith

end LocalizedProtocolErrors
end PermanssonResearch.ConstitutiveQuasi
