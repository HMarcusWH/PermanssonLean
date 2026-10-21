import PermanssonResearch.ReverseSolver.AdaptiveGrammarControl
import PermanssonResearch.GrammarRobust.AdversarialAdmission
import Mathlib.Tactic

/-!
D-08 restricted grammar and controlled-menu integration.

A CertifiedMenu admission predicate is linked to the *frozen*
restrictive partition rule. A concrete nonvacuous CertifiedMenu with
source-bound atom certificates is still a separate acceptance obligation.
-/
open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture
open PermanssonLean
open PermanssonResearch.GrammarRobust
open PermanssonResearch.GrammarRobust.BooleanDynamics
open PermanssonResearch.GrammarRobust.AdversarialAdmission
open PermanssonResearch.ReverseSolver.AdaptiveGrammarControl
set_option autoImplicit false

theorem forbidden_joint_not_in_restricted_menu
    {S X A C : Type*}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    [DecidableEq C] [Fintype C] {n : ℕ}
    (M : StrategicWorldModel S X A)
    (D : CertifiedMenu M C n)
    (names : PatchSelection S X A → Finset (Fin 2))
    (hlink : ∀ selection, D.admitted selection ↔
      AdversarialAdmission.restricted.allowed (names selection))
    (c : C)
    (hjoint : names (D.selection c) = joint) : False := by
  have hc : AdversarialAdmission.restricted.allowed (names (D.selection c)) :=
    (hlink _).mp (D.selection_admitted c)
  rw [hjoint] at hc
  exact AdversarialAdmission.restricted_joint_rejected hc

theorem admitted_block_row_normalized
    {S X A C : Type*}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    [DecidableEq C] [Fintype C] {n : ℕ}
    (M : StrategicWorldModel S X A) (D : CertifiedMenu M C n)
    (c : C) (y : Fin n) :
    (∑ z : Fin n, (D.rational c).entry y z) = 1 :=
  (D.rational c).row_sum_one y



namespace ConcreteRestrictedBoolean
open PermanssonLean
open MeasureTheory ProbabilityTheory
open PermanssonResearch.GrammarRobust
open PermanssonResearch.GrammarRobust.BooleanModel
open PermanssonResearch.GrammarRobust.BooleanBaseline
open PermanssonResearch.GrammarRobust.BooleanDynamics
open PermanssonResearch.GrammarRobust.AdversarialAdmission
open PermanssonResearch.ReverseSolver.AdaptiveGrammarControl
open PermanssonResearch.ReverseSolver.ControlledKernel

set_option autoImplicit false

/-- Explicit bijective native indexing of the original Bool strategic/world
state. No replacement of world X by a Fin 4 surrogate model. -/
def stateEquiv : Fin 4 ≃ Y :=
  (finProdFinEquiv (m := 2) (n := 2)).symm.trans
    (Equiv.prodCongr finTwoEquiv finTwoEquiv)

def stateIndex : Fin 4 ≃ᵐ Y where
  toEquiv := stateEquiv
  measurable_toFun := measurable_of_finite _
  measurable_invFun := measurable_of_finite _

/-- A genuine normalized rational row with the unique actual destination. -/
def atomRow (target : Fin 4) : RationalMarkovMatrix 4 where
  entry _ z := if z = target then 1 else 0
  entry_nonneg _ z := by split_ifs <;> norm_num
  row_sum_one _ := by simp

theorem dirac_atom_exact (dest : Y) (y z : Fin 4) :
    (Measure.dirac dest) {stateIndex z} =
      ENNReal.ofReal ((atomRow (stateIndex.symm dest)).entry y z : ℝ) := by
  by_cases hz : stateIndex z = dest
  · have htarget : z = stateIndex.symm dest := by
      apply stateIndex.injective
      simpa using hz
    simp [atomRow, hz, htarget, Measure.dirac_apply']
  · have htarget : z ≠ stateIndex.symm dest := by
      intro h
      apply hz
      simpa using congrArg stateIndex h
    simp [atomRow, hz, htarget, Measure.dirac_apply']

def actionSelection : PatchSelection Bool Bool Bool :=
  ([(bank.action (0 : Fin 1))], [])

def updateSelection : PatchSelection Bool Bool Bool :=
  ([], [(bank.update (0 : Fin 1))])

def chosen : Fin 2 → PatchSelection Bool Bool Bool
  | 0 => actionSelection
  | 1 => updateSelection

/-- Frozen syntactic grammar: nonempty action list names the action component,
nonempty update list names the update component. The joint patch is forbidden
even though each of the two individual replacement blocks is allowed. -/
def componentNames (b : PatchSelection Bool Bool Bool) : Finset (Fin 2) :=
  (if b.1.isEmpty then ∅ else {0}) ∪
    (if b.2.isEmpty then ∅ else {1})

theorem chosen_action_components :
    componentNames actionSelection = actionOnly := by
  simp [componentNames, actionSelection, actionOnly]

theorem chosen_update_components :
    componentNames updateSelection = updateOnly := by
  simp [componentNames, updateSelection, updateOnly]

noncomputable def actionSourceModel : StrategicWorldModel Bool Bool Bool :=
  overlapModel baseline actionSelection.1 actionSelection.2

noncomputable def updateSourceModel : StrategicWorldModel Bool Bool Bool :=
  overlapModel baseline updateSelection.1 updateSelection.2

/-- The actual alpha-P-U replacement still uses worldCopy and the true
source primitive U, not a selected rational matrix as a physical model. -/
theorem actionSourceModel_induced (y : Y) :
    actionSourceModel.inducedKernel y = Measure.dirac actionDest := by
  have hAlpha : actionSourceModel.generator.action = actionFalse := by
    apply Kernel.ext
    intro z
    have hz : z ∈ (bank.action (0 : Fin 1)).region := by simp [bank]
    have h := applyRowPatch_selected (bank.action (0 : Fin 1))
      (⟨baseline.generator.action, baseline.generator.action_isMarkov⟩ :
        MarkovKernelReplacement Y Bool) z hz
    simpa [actionSourceModel, actionSelection, overlapModel,
      applyCompatiblePatches, bank] using h
  have hUpdate : actionSourceModel.generator.update = updateTrue := by
    rfl
  apply Measure.ext
  intro E hE
  rw [StrategicWorldModel.inducedKernel_apply actionSourceModel y hE]
  rw [hAlpha, hUpdate]
  rw [overlapModel_world]
  simp [actionFalse, updateTrue, baseline, worldCopy,
    Kernel.deterministic_apply, Measure.dirac_apply, actionDest]
  by_cases hmem : (true,false) ∈ E <;> simp [hmem]

theorem updateSourceModel_induced (y : Y) :
    updateSourceModel.inducedKernel y = Measure.dirac updateDest := by
  have hAlpha : updateSourceModel.generator.action = actionTrue := by rfl
  have hUpdate : updateSourceModel.generator.update = updateFalse := by
    apply Kernel.ext
    intro z
    have hz : z ∈ (bank.update (0 : Fin 1)).region := by simp [bank]
    have h := applyRowPatch_selected (bank.update (0 : Fin 1))
      (⟨baseline.generator.update, baseline.generator.update_isMarkov⟩ :
        MarkovKernelReplacement (UpdateInput Bool Bool Bool) Bool) z hz
    simpa [updateSourceModel, updateSelection, overlapModel,
      applyCompatiblePatches, bank] using h
  apply Measure.ext
  intro E hE
  rw [StrategicWorldModel.inducedKernel_apply updateSourceModel y hE]
  rw [hAlpha, hUpdate]
  rw [overlapModel_world]
  simp [actionTrue, updateFalse, baseline, worldCopy,
    Kernel.deterministic_apply, Measure.dirac_apply, updateDest]
  by_cases hmem : (false,true) ∈ E <;> simp [hmem]

/-- NON-VACUOUS controlled menu. Two genuinely different admitted strategic
patches, both nonempty action sets and a normalized exact stochastic row
on each of the four source states, all tied to frozen restrictive grammar. -/
noncomputable def restrictedCertifiedMenu : CertifiedMenu baseline (Fin 2) 4 where
  stateIndex := stateIndex
  states_nonempty := by decide
  baseline := atomRow (stateIndex.symm q0)
  baseline_atom_certificate := by
    intro y z
    rw [inducedKernel_dirac]
    exact dirac_atom_exact q0 y z
  selection := chosen
  admitted := fun b => restricted.allowed (componentNames b)
  selection_admitted := by
    intro c
    fin_cases c
    · simpa [chosen, chosen_action_components] using restricted_action_allowed
    · simpa [chosen, chosen_update_components] using restricted_update_allowed
  compatible_action := by
    intro c p hp q hq
    fin_cases c <;> simp_all [chosen, actionSelection, updateSelection,
      RowPatch.Compatible]
  compatible_update := by
    intro c p hp q hq
    fin_cases c <;> simp_all [chosen, actionSelection, updateSelection,
      RowPatch.Compatible]
  options := fun _ => Finset.univ
  options_nonempty := by
    intro y
    exact ⟨0, Finset.mem_univ _⟩
  rational := fun c =>
    if c = 0 then atomRow (stateIndex.symm actionDest)
    else atomRow (stateIndex.symm updateDest)
  atom_certificate := by
    intro c y z
    fin_cases c
    · change actionSourceModel.inducedKernel (stateIndex y) {stateIndex z} =
        ENNReal.ofReal ((atomRow (stateIndex.symm actionDest)).entry y z : ℝ)
      rw [actionSourceModel_induced]
      exact dirac_atom_exact actionDest y z
    · change updateSourceModel.inducedKernel (stateIndex y) {stateIndex z} =
        ENNReal.ofReal ((atomRow (stateIndex.symm updateDest)).entry y z : ℝ)
      rw [updateSourceModel_induced]
      exact dirac_atom_exact updateDest y z

theorem actual_restricted_menu_admits_both_components :
    restrictedCertifiedMenu.selection_admitted (0 : Fin 2) ∧
    restrictedCertifiedMenu.selection_admitted (1 : Fin 2) :=
  ⟨restrictedCertifiedMenu.selection_admitted 0,
   restrictedCertifiedMenu.selection_admitted 1⟩

theorem actual_restricted_menu_rejects_joint :
    ¬ ∃ c : Fin 2,
        componentNames (restrictedCertifiedMenu.selection c) = joint := by
  rintro ⟨c,hc⟩
  exact forbidden_joint_not_in_restricted_menu baseline
    restrictedCertifiedMenu componentNames (by intro b; rfl) c hc

theorem actual_restricted_menu_row_normalized (c : Fin 2) (y : Fin 4) :
    ∑ z : Fin 4, (restrictedCertifiedMenu.rational c).entry y z = 1 :=
  admitted_block_row_normalized baseline restrictedCertifiedMenu c y

end ConcreteRestrictedBoolean

end PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture
