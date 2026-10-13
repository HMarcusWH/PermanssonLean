import PermanssonResearch.ReverseSolver.RationalTypedSupportBridge
import PermanssonResearch.MultipleLimit.ExactSixStateC8SupportWitness
import PermanssonResearch.MultipleLimit.ExactSixStateConstitution
import PermanssonResearch.MultipleLimit.ExactSixStateObservedGR
import Mathlib.Tactic

/-!
# C9-06 — original six-state frozen-menu feasibility, rejection, and optimizer

The ORIGINAL baseline has an independently proved Exact GR and a genuinely
nontrivial original B₁ containing u and a0. A three-member menu contains
C6 full disruption (Lean-proved margin 1) and C8 half/tiny responses
(actual typed admissible strategic alpha changes with common P/U).
Because a genuine Boolean event effect cannot exceed 1, full disruption
is certified a global menu maximizer without assuming Python's half/tiny
numerical margins as Lean theorem premises.

Additional genuine typed identity and one-row-only negative interventions
are constructed here, instead of treating Python fixtures as Lean data.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace ReverseSolver
namespace ExactSixStateC9MenuWitness

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.MultipleLimit
open PermanssonResearch.MultipleLimit.ExactSixState
open PermanssonResearch.MultipleLimit.ExactSixStateCanonical
open PermanssonResearch.MultipleLimit.ExactSixStateTyped
open PermanssonResearch.MultipleLimit.ExactSixStateObservedGR
open PermanssonResearch.MultipleLimit.ExactSixStateTargetDisruption
open PermanssonResearch.MultipleLimit.ExactSixStateC8SupportWitness
open PermanssonResearch.MultipleLimit.ExactSixStateConstitution
open PermanssonResearch.MultipleLimit.FrozenObservedEvent
open PermanssonResearch.MultipleLimit.TypedObservedEventConstitution
open PermanssonResearch.MultipleLimit.FiniteObservedUniformMargin
open PermanssonResearch.MultipleLimit.OppositeClassConstitutiveMargin
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.FiniteObservedClassSupport
open PermanssonResearch.MultipleLimit.FiniteObservedBadClassReachability
open FiniteStrategicRealization
open FrozenConstitutiveMenu
open MenuConstitutionClassification
open MenuFeasibilityCertificates
open MenuMarginOptimization
open RationalTypedSupportBridge

noncomputable section

abbrev SixY := JointState Unit (Fin 6)

/-- Genuine typed D0 menu, with exactly three indices:
0 = C6 full disruption, 1 = C8 half, 2 = C8 tiny. -/
def threeMemberMenu :
    FrozenMenu typedModel (researchActionFamily sixStateMatrix) (Fin 3) where
  indices := Finset.univ
  nonempty := ⟨0, Finset.mem_univ 0⟩
  choice := fun i =>
    if i = 0 then ExactSixStateTargetDisruption.intervention
    else if i = 1 then halfJ
    else tinyJ

theorem three_full_originalPR :
    IsUniformGeneralizedPermanssonRegimeRelative
      typedModel observedSpec observedReference
      (researchActionFamily sixStateMatrix)
      (eventuallyObservedProperty observedDescriptor true)
      comparison (threeMemberMenu.choice (0 : Fin 3)) := by
  simpa [threeMemberMenu, TypedEventResponse.fixedProperty] using
    ExactSixStateConstitution.uniformRelativePR

theorem three_half_originalPR :
    IsUniformGeneralizedPermanssonRegimeRelative
      typedModel observedSpec observedReference
      (researchActionFamily sixStateMatrix)
      (eventuallyObservedProperty observedDescriptor true)
      comparison (threeMemberMenu.choice (1 : Fin 3)) := by
  simpa [threeMemberMenu] using half_uniformRelativePR

theorem three_tiny_originalPR :
    IsUniformGeneralizedPermanssonRegimeRelative
      typedModel observedSpec observedReference
      (researchActionFamily sixStateMatrix)
      (eventuallyObservedProperty observedDescriptor true)
      comparison (threeMemberMenu.choice (2 : Fin 3)) := by
  simpa [threeMemberMenu] using tiny_uniformRelativePR

/-- All three candidate indices are in the exact structural eligible
subset of the frozen menu. -/
theorem three_all_eligible (i : Fin 3) :
    i ∈ supportEligibleIndices typedModel observedSpec
      (researchActionFamily sixStateMatrix) comparison threeMemberMenu := by
  have hGR := observedExactGeneratedRegime
  have hmode : observedSpec.convergenceMode =
      ConvergenceMode.almostSureWeak SixY Bool := rfl
  have hmem : i ∈ threeMemberMenu.indices := by
    simp [threeMemberMenu]
  have hPR : IsUniformGeneralizedPermanssonRegimeRelative
      typedModel observedSpec observedReference
      (researchActionFamily sixStateMatrix)
      (eventuallyObservedProperty observedDescriptor true)
      comparison (threeMemberMenu.choice i) := by
    fin_cases i
    · exact three_full_originalPR
    · exact three_half_originalPR
    · exact three_tiny_originalPR
  have he := ((listed_uniformPR_iff_exactGR_and_support
    typedModel observedSpec observedReference
    (researchActionFamily sixStateMatrix)
    comparison threeMemberMenu hmode i).mp hPR).2
  exact (supportEligibleIndices_mem_iff
    typedModel observedSpec (researchActionFamily sixStateMatrix)
    comparison threeMemberMenu i).mpr ⟨hmem, he⟩

/-- The already certified C6 actual original margin is exactly 1,
not a rational Python approximation. -/
theorem full_actual_margin_one :
    menuConstitutiveMargin typedModel observedSpec
      (researchActionFamily sixStateMatrix)
      comparison threeMemberMenu (0 : Fin 3) = 1 := by
  have h := ExactSixStateConstitution.constitutiveMargin_eq_one
  change constitutiveMargin typedModel observedSpec
      (researchActionFamily sixStateMatrix)
      (eventuallyObservedProperty observedDescriptor true)
      comparison ExactSixStateTargetDisruption.intervention = 1 at h
  change constitutiveMargin typedModel observedSpec
    (researchActionFamily sixStateMatrix)
    (eventuallyObservedProperty observedDescriptor true)
    comparison (threeMemberMenu.choice (0 : Fin 3)) = 1
  simpa [threeMemberMenu] using h

/-- A certified named GLOBAL optimizer of actual original margins:
the C6 full disruption beats or ties every listed candidate since all
Boolean-event margins are bounded by 1. No unique optimum claimed. -/
theorem full_is_global_margin_maximizer :
    (0 : Fin 3) ∈ threeMemberMenu.indices ∧
    ∀ i ∈ threeMemberMenu.indices,
      menuConstitutiveMargin typedModel observedSpec
        (researchActionFamily sixStateMatrix)
        comparison threeMemberMenu i ≤
      menuConstitutiveMargin typedModel observedSpec
        (researchActionFamily sixStateMatrix)
        comparison threeMemberMenu (0 : Fin 3) := by
  constructor
  · simp [threeMemberMenu]
  · intro i hi
    rw [full_actual_margin_one]
    exact eventConstitutiveMargin_le_one typedModel observedSpec
      (researchActionFamily sixStateMatrix)
      comparison (threeMemberMenu.choice i)

/-- The two C8 candidates remain distinct quantitative choices in
the same qualitative support class. No margin equality is asserted. -/
theorem half_tiny_equal_support :
    PermanssonResearch.MultipleLimit.ObservedSupportInvariance.SamePositiveSupport
      (threeMemberMenu.choice (1 : Fin 3)).intervention.apply.inducedKernel
      (threeMemberMenu.choice (2 : Fin 3)).intervention.apply.inducedKernel := by
  change PermanssonResearch.MultipleLimit.ObservedSupportInvariance.SamePositiveSupport
    halfJ.intervention.apply.inducedKernel
    tinyJ.intervention.apply.inducedKernel
  exact same_intervened_positive_support

theorem three_member_world_fixed (i : Fin 3) :
    (threeMemberMenu.choice i).intervention.apply.world =
      typedModel.world :=
  (threeMemberMenu.choice i).world_eq

/-- U is fixed in this PARTICULAR D0 alpha-only constructed family,
which is stronger than generic strategic-admissibility's fixed P. -/
theorem three_member_update_fixed (i : Fin 3) :
    (threeMemberMenu.choice i).intervention.apply.generator.update =
      typedModel.generator.update := by
  fin_cases i
  · change ExactSixStateTargetDisruption.intervention.intervention.apply.generator.update =
        typedModel.generator.update
    rw [ExactSixStateTargetDisruption.intervention_apply]
    exact ExactSixStateTargetDisruption.intervention_update_fixed
  · change halfJ.intervention.apply.generator.update = typedModel.generator.update
    exact half_update_fixed
  · change tinyJ.intervention.apply.generator.update = typedModel.generator.update
    exact tiny_update_fixed

/-- Actual typed identity choice on the ORIGINAL frozen baseline. -/
def identityJ : AdmissibleStrategicIntervention
    (researchActionFamily sixStateMatrix) :=
  rationalStrategicIntervention sixStateMatrix sixStateMatrix

theorem identity_actual_margin_zero :
    constitutiveMargin typedModel observedSpec
      (researchActionFamily sixStateMatrix)
      (eventuallyObservedProperty observedDescriptor true)
      comparison identityJ = 0 := by
  obtain ⟨y, hy, hmin⟩ := finite_margin_attained
    typedModel observedSpec (researchActionFamily sixStateMatrix)
    (eventuallyObservedProperty observedDescriptor true)
    comparison identityJ
  rw [hmin, effect_eq_abs_goodMass_difference typedModel
    (researchActionFamily sixStateMatrix) identityJ observedDescriptor y]
  change |(pointGoodMass typedModel.inducedKernel observedDescriptor y).toReal -
      (pointGoodMass typedModel.inducedKernel observedDescriptor y).toReal| = 0
  simp

/-- One-row-only sparse intervention: u becomes absorbing;
the physical A rows (2,3) retain the ORIGINAL closed period-two class. -/
def oneRowEntry (i j : Fin 6) : ℚ :=
  if i = 1 then
    if j = 1 then 1 else 0
  else transition i j

theorem oneRowEntry_nonneg (i j : Fin 6) : 0 ≤ oneRowEntry i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [oneRowEntry, transition]

theorem oneRowEntry_row_sum (i : Fin 6) :
    (∑ j : Fin 6, oneRowEntry i j) = 1 := by
  fin_cases i <;>
    norm_num [oneRowEntry, transition, Fin.sum_univ_succ]

def oneRowMatrix : RationalMarkovMatrix 6 where
  entry := oneRowEntry
  entry_nonneg := oneRowEntry_nonneg
  row_sum_one := oneRowEntry_row_sum

/-- A second newly constructed genuine alpha-only typed negative
candidate, not a Python fixture passed off as a Lean intervention. -/
def oneRowJ : AdmissibleStrategicIntervention
    (researchActionFamily sixStateMatrix) :=
  rationalStrategicIntervention sixStateMatrix oneRowMatrix

private abbrev Kone := oneRowJ.intervention.apply.inducedKernel

def phaseA : Set SixY :=
  {decode (2 : Fin 6), decode (3 : Fin 6)}

theorem phaseA_descriptor_true (y : SixY) (hy : y ∈ phaseA) :
    observedDescriptor y = true := by
  change y = decode (2 : Fin 6) ∨ y = decode (3 : Fin 6) at hy
  rcases hy with rfl | rfl <;>
    norm_num [observedDescriptor, observedRecurrent, encode, decode]

/-- The actual one-row typed induced kernel retains physical closed A. -/
theorem oneRow_phaseA_closed : ClosedSubset Kone phaseA := by
  intro y hy z hedge
  change y = decode (2 : Fin 6) ∨ y = decode (3 : Fin 6) at hy
  rcases z with ⟨u, j⟩
  cases u
  rcases hy with hy | hy
  · subst y
    have hp := (rationalTyped_positiveEdge_iff
      sixStateMatrix oneRowMatrix (2 : Fin 6) j).mp hedge
    change 0 < oneRowEntry (2 : Fin 6) j at hp
    fin_cases j <;>
      (try norm_num [oneRowEntry, transition] at hp)
    all_goals simp [phaseA, decode]
  · subst y
    have hp := (rationalTyped_positiveEdge_iff
      sixStateMatrix oneRowMatrix (3 : Fin 6) j).mp hedge
    change 0 < oneRowEntry (3 : Fin 6) j at hp
    fin_cases j <;>
      (try norm_num [oneRowEntry, transition] at hp)
    all_goals simp [phaseA, decode]

/-- From the ORIGINAL second comparison state a0, no BAD recurrent
class is graph-reachable under this one-row-only typed intervention. -/
theorem oneRow_not_opposing_from_a0 :
    ¬ OpposingClassReachable Kone observedDescriptor
      observedSpec.target (decode (2 : Fin 6)) := by
  have ht : observedSpec.target = diracProba true := rfl
  simp only [OpposingClassReachable, if_pos ht]
  rintro ⟨i, hiBad, hiReach⟩
  have h2 : decode (2 : Fin 6) ∈ phaseA := by
    simp [phaseA]
  have hiA : i ∈ phaseA :=
    closed_reachable Kone oneRow_phaseA_closed h2 hiReach
  have hgood : AllTrueClass Kone observedDescriptor i := by
    intro z hz
    exact phaseA_descriptor_true z
      (closed_reachable Kone oneRow_phaseA_closed hiA hz.1)
  exact (Finset.mem_filter.mp hiBad).2 hgood

/-- A frozen TWO-CANDIDATE genuine typed negative menu. -/
def negativeMenu :
    FrozenMenu typedModel (researchActionFamily sixStateMatrix) (Fin 2) where
  indices := Finset.univ
  nonempty := ⟨0, Finset.mem_univ 0⟩
  choice := fun i => if i = 0 then identityJ else oneRowJ

theorem negativeMenu_eligible_empty :
    supportEligibleIndices typedModel observedSpec
      (researchActionFamily sixStateMatrix) comparison negativeMenu = ∅ := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    have hitem := (supportEligibleIndices_mem_iff
      typedModel observedSpec (researchActionFamily sixStateMatrix)
      comparison negativeMenu i).mp hi
    fin_cases i
    · have hz : menuConstitutiveMargin typedModel observedSpec
          (researchActionFamily sixStateMatrix)
          comparison negativeMenu (0 : Fin 2) = 0 := by
        change constitutiveMargin typedModel observedSpec
          (researchActionFamily sixStateMatrix)
          (eventuallyObservedProperty observedDescriptor true)
          comparison identityJ = 0
        exact identity_actual_margin_zero
      have hnot := (margin_eq_zero_iff_not_support_of_exactGR
        typedModel observedSpec observedReference
        (researchActionFamily sixStateMatrix)
        comparison negativeMenu observedExactGeneratedRegime
        (show observedSpec.convergenceMode =
          ConvergenceMode.almostSureWeak SixY Bool from rfl)
        (0 : Fin 2)).mp hz
      exact (hnot hitem.2).elim
    · have hnot : ¬ menuSupportEligible typedModel observedSpec
          (researchActionFamily sixStateMatrix) comparison
          negativeMenu (1 : Fin 2) := by
        intro he
        have ha : decode (2 : Fin 6) ∈ comparison.states :=
          (comparison_states _).mpr (Or.inr rfl)
        have hbad := he (decode (2 : Fin 6)) ha
        exact oneRow_not_opposing_from_a0 (by
          simpa [negativeMenu, menuSupportEligible] using hbad)
      exact (hnot hitem.2).elim
  · intro hempty
    simpa using hempty

/-- The original menu is INFEASIBLE over its two listed members
only; C6's separate unlisted full intervention is still a family PR! -/
theorem negativeMenu_all_listed_not_PR :
    ∀ i ∈ negativeMenu.indices,
      ¬ IsUniformGeneralizedPermanssonRegimeRelative
        typedModel observedSpec observedReference
        (researchActionFamily sixStateMatrix)
        (eventuallyObservedProperty observedDescriptor true)
        comparison (negativeMenu.choice i) := by
  have hmode : observedSpec.convergenceMode =
      ConvergenceMode.almostSureWeak SixY Bool := rfl
  exact (empty_eligible_iff_no_listed_PR_of_exactGR
    typedModel observedSpec observedReference
    (researchActionFamily sixStateMatrix)
    comparison negativeMenu observedExactGeneratedRegime hmode).mp
      negativeMenu_eligible_empty

end
end ExactSixStateC9MenuWitness
end ReverseSolver
end PermanssonResearch
