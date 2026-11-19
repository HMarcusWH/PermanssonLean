import PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture
import PermanssonResearch.GrammarRobust.JointOnlyCertifiedFixture
import PermanssonResearch.GrammarRobust.BooleanOverlapFixture
import Mathlib.Tactic

/-!
# Tranche 9: original D-08 typed admission and compatible overlap

This addendum addresses the original D-08 criterion: an illegal or conflicting
controller block has no admissible CertifiedMenu choice. It does not claim that
an arbitrary raw list of Markov row patches has no normalized fold. Indeed,
the raw conflicting folds below both exist and depend on their order.

The existing restricted menu admits separate action and update components.
Its single-patch lists do not witness two distinct overlapping action patches.
Here a new localized action patch genuinely overlaps the original full-domain
action patch. They agree on the overlap, inhabit an actual CertifiedMenu on
the unchanged Boolean alpha-P-U source, and retain the original rational rows,
grammar predicate, four-state indexing and physical kernel.

A conflicting localized patch cannot coexist with the false patch in any
CertifiedMenu choice for this source. Separately, the existing fine grammar's
OR joint-only positive margin is audited without conflating it with admission
under the restricted grammar. Original D-08 and later claim D8 remain distinct
certification entries; this file grants neither independent acceptance.
-/

open MeasureTheory ProbabilityTheory Set
open PermanssonLean

namespace PermanssonResearch.Certification.Tranche9D08

open PermanssonResearch.GrammarRobust
open PermanssonResearch.GrammarRobust.BooleanModel
open PermanssonResearch.GrammarRobust.BooleanBaseline
open PermanssonResearch.GrammarRobust.BooleanDynamics
open PermanssonResearch.GrammarRobust.AdversarialAdmission
open PermanssonResearch.ReverseSolver.AdaptiveGrammarControl
open PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture
open PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture.ConcreteRestrictedBoolean

set_option autoImplicit false

/-- A proper local mask on the original strategic/world input space. -/
noncomputable def localFalsePatch : RowPatch Y Bool where
  region := {q1}
  measurable_region := MeasurableSet.of_discrete
  replacement := actionFalse
  replacement_isMarkov := by unfold actionFalse; infer_instance

/-- The same local mask with a conflicting actual action row. -/
noncomputable def localTruePatch : RowPatch Y Bool where
  region := {q1}
  measurable_region := MeasurableSet.of_discrete
  replacement := actionTrue
  replacement_isMarkov := by unfold actionTrue; infer_instance

theorem localized_and_wide_patches_distinct :
    localFalsePatch ≠ bank.action (0 : Fin 1) := by
  intro h
  have hmem : q0 ∈ localFalsePatch.region := by
    rw [h]
    simp [bank]
  simp [localFalsePatch, q0, q1] at hmem

theorem original_input_has_genuine_overlap :
    q1 ∈ localFalsePatch.region ∧ q1 ∈ (bank.action (0 : Fin 1)).region := by
  simp [localFalsePatch, bank]

theorem compatible_action_patch_pair :
    ∀ p ∈ [localFalsePatch, bank.action (0 : Fin 1)],
      ∀ q ∈ [localFalsePatch, bank.action (0 : Fin 1)], p.Compatible q := by
  intro p hp q hq
  simp at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    intro y hy hz <;> rfl

noncomputable def compatibleSelection : PatchSelection Bool Bool Bool :=
  ([localFalsePatch, bank.action (0 : Fin 1)], [])

noncomputable def compatibleChoices : Fin 2 → PatchSelection Bool Bool Bool
  | 0 => compatibleSelection
  | 1 => updateSelection

noncomputable def compatibleActionModel : StrategicWorldModel Bool Bool Bool :=
  overlapModel baseline compatibleSelection.1 compatibleSelection.2

theorem compatible_original_action_row (y : Y) :
    compatibleActionModel.generator.action y = actionFalse y := by
  change
    (applyCompatiblePatches [localFalsePatch, bank.action (0 : Fin 1)]
      (⟨baseline.generator.action, baseline.generator.action_isMarkov⟩ :
        MarkovKernelReplacement Y Bool)).kernel y = actionFalse y
  have h := applyCompatiblePatches_active
    [localFalsePatch, bank.action (0 : Fin 1)] compatible_action_patch_pair
    (⟨baseline.generator.action, baseline.generator.action_isMarkov⟩ :
      MarkovKernelReplacement Y Bool)
    (bank.action (0 : Fin 1)) (by simp) y (by simp [bank])
  simpa [bank] using h

/-- Exact original alpha-P-U row, not an independently chosen rational model. -/
theorem compatible_original_induced_row (y : Y) :
    compatibleActionModel.inducedKernel y = Measure.dirac actionDest := by
  have hAlpha : compatibleActionModel.generator.action = actionFalse := by
    apply Kernel.ext
    intro z
    exact compatible_original_action_row z
  have hUpdate : compatibleActionModel.generator.update = updateTrue := rfl
  apply Measure.ext
  intro E hE
  rw [StrategicWorldModel.inducedKernel_apply compatibleActionModel y hE]
  rw [hAlpha, hUpdate]
  have hWorld : compatibleActionModel.world = worldCopy := rfl
  rw [hWorld]
  simp [actionFalse, updateTrue, baseline, worldCopy,
    Kernel.deterministic_apply, Measure.dirac_apply, actionDest]
  by_cases hmem : (true, false) ∈ E <;> simp [hmem]

/-- Nonvacuous compatible overlap inside an actual typed certified menu.
Only the first choice's action list changes; the second choice, admission
predicate, rational matrices, indexing and physical source are retained. -/
noncomputable def compatibleOverlapMenu : CertifiedMenu baseline (Fin 2) 4 :=
  { restrictedCertifiedMenu with
    selection := compatibleChoices
    selection_admitted := by
      intro c
      fin_cases c
      · change restricted.allowed (componentNames compatibleSelection)
        have hnames : componentNames compatibleSelection = actionOnly := by
          simp [componentNames, compatibleSelection, actionOnly]
        rw [hnames]
        exact restricted_action_allowed
      · change restricted.allowed (componentNames updateSelection)
        rw [chosen_update_components]
        exact restricted_update_allowed
    compatible_action := by
      intro c
      fin_cases c
      · exact compatible_action_patch_pair
      · intro p hp
        simp [compatibleChoices, updateSelection] at hp
    compatible_update := by
      intro c
      fin_cases c
      · intro p hp
        simp [compatibleChoices, compatibleSelection] at hp
      · intro p hp q hq
        simp [compatibleChoices, updateSelection] at hp hq
        subst p
        subst q
        intro y hy hz
        rfl
    atom_certificate := by
      intro c y z
      fin_cases c
      · change compatibleActionModel.inducedKernel (stateIndex y) {stateIndex z} =
          ENNReal.ofReal ((atomRow (stateIndex.symm actionDest)).entry y z : ℝ)
        rw [compatible_original_induced_row]
        exact dirac_atom_exact actionDest y z
      · change updateSourceModel.inducedKernel (stateIndex y) {stateIndex z} =
          ENNReal.ofReal ((atomRow (stateIndex.symm updateDest)).entry y z : ℝ)
        rw [updateSourceModel_induced]
        exact dirac_atom_exact updateDest y z }

/-- The two genuinely distinct patches occur together in a selected block. -/
theorem actual_menu_contains_two_compatible_patches :
    (compatibleOverlapMenu.selection (0 : Fin 2)).1 =
      [localFalsePatch, bank.action (0 : Fin 1)] ∧
    localFalsePatch ≠ bank.action (0 : Fin 1) ∧
    q1 ∈ localFalsePatch.region ∧ q1 ∈ (bank.action (0 : Fin 1)).region :=
  ⟨rfl, localized_and_wide_patches_distinct, original_input_has_genuine_overlap⟩

theorem actual_compatible_menu_admits_both_choices :
    compatibleOverlapMenu.admitted (compatibleOverlapMenu.selection (0 : Fin 2)) ∧
    compatibleOverlapMenu.admitted (compatibleOverlapMenu.selection (1 : Fin 2)) :=
  ⟨compatibleOverlapMenu.selection_admitted 0,
   compatibleOverlapMenu.selection_admitted 1⟩

theorem actual_compatible_menu_world_frozen (c : Fin 2) :
    (blockModel baseline compatibleOverlapMenu c).world = baseline.world :=
  block_preserves_world baseline compatibleOverlapMenu c

theorem actual_compatible_menu_typed_row_exact (c : Fin 2) (y z : Fin 4) :
    typedRow baseline compatibleOverlapMenu c y z =
      ((compatibleOverlapMenu.rational c).entry y z : ℝ) :=
  typedRow_eq baseline compatibleOverlapMenu c y z

theorem actual_compatible_menu_typed_row_normalized (c : Fin 2) (y : Fin 4) :
    ∑ z : Fin 4, typedRow baseline compatibleOverlapMenu c y z = 1 := by
  simp_rw [actual_compatible_menu_typed_row_exact]
  have h := (compatibleOverlapMenu.rational c).row_sum_one y
  exact_mod_cast h

theorem actual_compatible_menu_rejects_joint :
    ¬ ∃ c : Fin 2, componentNames (compatibleOverlapMenu.selection c) = joint := by
  rintro ⟨c, hc⟩
  exact forbidden_joint_not_in_restricted_menu baseline
    compatibleOverlapMenu componentNames (by intro b; rfl) c hc

theorem localized_action_patches_conflict :
    ¬ localFalsePatch.Compatible localTruePatch := by
  intro hc
  have rowEq := hc q1 (by simp [localFalsePatch]) (by simp [localTruePatch])
  have hmass := congrArg (fun μ : Measure Bool => μ {true}) rowEq
  simp [localFalsePatch, localTruePatch, actionFalse, actionTrue,
    Kernel.deterministic_apply] at hmass

/-- No choice in ANY certified menu on this original source can contain
both conflicting action patches. This is a typed compatibility obstruction. -/
theorem no_certified_choice_with_conflicting_pair
    {C : Type*} [DecidableEq C] (D : CertifiedMenu baseline C 4) :
    ¬ ∃ c : C,
      localFalsePatch ∈ (D.selection c).1 ∧ localTruePatch ∈ (D.selection c).1 := by
  rintro ⟨c, hp, hq⟩
  exact localized_action_patches_conflict
    (D.compatible_action c localFalsePatch hp localTruePatch hq)

/-- Raw Markov patch folds still exist, but conflict makes their order
observable. Their existence is not a CertifiedMenu admission certificate. -/
theorem raw_conflicting_orders_differ :
    (applyCompatiblePatches [localFalsePatch, localTruePatch]
      (⟨baseline.generator.action, baseline.generator.action_isMarkov⟩ :
        MarkovKernelReplacement Y Bool)).kernel q1 ≠
    (applyCompatiblePatches [localTruePatch, localFalsePatch]
      (⟨baseline.generator.action, baseline.generator.action_isMarkov⟩ :
        MarkovKernelReplacement Y Bool)).kernel q1 := by
  have hf :
      (applyCompatiblePatches [localFalsePatch, localTruePatch]
        (⟨baseline.generator.action, baseline.generator.action_isMarkov⟩ :
          MarkovKernelReplacement Y Bool)).kernel q1 = actionFalse q1 := by
    change (applyRowPatch localFalsePatch
      (applyRowPatch localTruePatch
        (⟨baseline.generator.action, baseline.generator.action_isMarkov⟩ :
          MarkovKernelReplacement Y Bool))).kernel q1 = actionFalse q1
    exact applyRowPatch_selected localFalsePatch _ q1 (by simp [localFalsePatch])
  have ht :
      (applyCompatiblePatches [localTruePatch, localFalsePatch]
        (⟨baseline.generator.action, baseline.generator.action_isMarkov⟩ :
          MarkovKernelReplacement Y Bool)).kernel q1 = actionTrue q1 := by
    change (applyRowPatch localTruePatch
      (applyRowPatch localFalsePatch
        (⟨baseline.generator.action, baseline.generator.action_isMarkov⟩ :
          MarkovKernelReplacement Y Bool))).kernel q1 = actionTrue q1
    exact applyRowPatch_selected localTruePatch _ q1 (by simp [localTruePatch])
  intro heq
  rw [hf, ht] at heq
  have hmass := congrArg (fun μ : Measure Bool => μ {true}) heq
  simp [actionFalse, actionTrue, Kernel.deterministic_apply] at hmass

end PermanssonResearch.Certification.Tranche9D08

-- ORIGINAL_TYPED_ADMISSION_CONTRACT
#check PermanssonResearch.ReverseSolver.AdaptiveGrammarControl.CertifiedMenu
#print axioms PermanssonResearch.ReverseSolver.AdaptiveGrammarControl.CertifiedMenu
#check PermanssonResearch.ReverseSolver.AdaptiveGrammarControl.block_preserves_world
#print axioms PermanssonResearch.ReverseSolver.AdaptiveGrammarControl.block_preserves_world
#check PermanssonResearch.ReverseSolver.AdaptiveGrammarControl.typedRow_eq
#print axioms PermanssonResearch.ReverseSolver.AdaptiveGrammarControl.typedRow_eq
#check PermanssonResearch.ReverseSolver.AdaptiveGrammarControl.typedChronologicalLaw_eq
#print axioms PermanssonResearch.ReverseSolver.AdaptiveGrammarControl.typedChronologicalLaw_eq
#check PermanssonResearch.GrammarRobust.AdversarialAdmission.restricted_action_allowed
#print axioms PermanssonResearch.GrammarRobust.AdversarialAdmission.restricted_action_allowed
#check PermanssonResearch.GrammarRobust.AdversarialAdmission.restricted_update_allowed
#print axioms PermanssonResearch.GrammarRobust.AdversarialAdmission.restricted_update_allowed
#check PermanssonResearch.GrammarRobust.AdversarialAdmission.restricted_joint_rejected
#print axioms PermanssonResearch.GrammarRobust.AdversarialAdmission.restricted_joint_rejected
#check PermanssonResearch.GrammarRobust.AdversarialAdmission.forbidden_block_has_no_certificate
#print axioms PermanssonResearch.GrammarRobust.AdversarialAdmission.forbidden_block_has_no_certificate

-- HISTORICAL_RESTRICTED_MENU
#check PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture.ConcreteRestrictedBoolean.actual_restricted_menu_admits_both_components
#print axioms PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture.ConcreteRestrictedBoolean.actual_restricted_menu_admits_both_components
#check PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture.ConcreteRestrictedBoolean.actual_restricted_menu_rejects_joint
#print axioms PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture.ConcreteRestrictedBoolean.actual_restricted_menu_rejects_joint
#check PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture.ConcreteRestrictedBoolean.actual_restricted_menu_row_normalized
#print axioms PermanssonResearch.ReverseSolver.AdaptiveGrammarAdmissionFixture.ConcreteRestrictedBoolean.actual_restricted_menu_row_normalized

-- NEW_NONVACUOUS_COMPATIBLE_OVERLAP
#check PermanssonResearch.Certification.Tranche9D08.localized_and_wide_patches_distinct
#print axioms PermanssonResearch.Certification.Tranche9D08.localized_and_wide_patches_distinct
#check PermanssonResearch.Certification.Tranche9D08.original_input_has_genuine_overlap
#print axioms PermanssonResearch.Certification.Tranche9D08.original_input_has_genuine_overlap
#check PermanssonResearch.Certification.Tranche9D08.compatible_action_patch_pair
#print axioms PermanssonResearch.Certification.Tranche9D08.compatible_action_patch_pair
#check PermanssonResearch.Certification.Tranche9D08.compatible_original_action_row
#print axioms PermanssonResearch.Certification.Tranche9D08.compatible_original_action_row
#check PermanssonResearch.Certification.Tranche9D08.compatible_original_induced_row
#print axioms PermanssonResearch.Certification.Tranche9D08.compatible_original_induced_row
#check PermanssonResearch.Certification.Tranche9D08.compatibleOverlapMenu
#print axioms PermanssonResearch.Certification.Tranche9D08.compatibleOverlapMenu
#check PermanssonResearch.Certification.Tranche9D08.actual_menu_contains_two_compatible_patches
#print axioms PermanssonResearch.Certification.Tranche9D08.actual_menu_contains_two_compatible_patches
#check PermanssonResearch.Certification.Tranche9D08.actual_compatible_menu_admits_both_choices
#print axioms PermanssonResearch.Certification.Tranche9D08.actual_compatible_menu_admits_both_choices
#check PermanssonResearch.Certification.Tranche9D08.actual_compatible_menu_world_frozen
#print axioms PermanssonResearch.Certification.Tranche9D08.actual_compatible_menu_world_frozen
#check PermanssonResearch.Certification.Tranche9D08.actual_compatible_menu_typed_row_exact
#print axioms PermanssonResearch.Certification.Tranche9D08.actual_compatible_menu_typed_row_exact
#check PermanssonResearch.Certification.Tranche9D08.actual_compatible_menu_typed_row_normalized
#print axioms PermanssonResearch.Certification.Tranche9D08.actual_compatible_menu_typed_row_normalized
#check PermanssonResearch.Certification.Tranche9D08.actual_compatible_menu_rejects_joint
#print axioms PermanssonResearch.Certification.Tranche9D08.actual_compatible_menu_rejects_joint
#check PermanssonResearch.Certification.Tranche9D08.localized_action_patches_conflict
#print axioms PermanssonResearch.Certification.Tranche9D08.localized_action_patches_conflict
#check PermanssonResearch.Certification.Tranche9D08.no_certified_choice_with_conflicting_pair
#print axioms PermanssonResearch.Certification.Tranche9D08.no_certified_choice_with_conflicting_pair
#check PermanssonResearch.Certification.Tranche9D08.raw_conflicting_orders_differ
#print axioms PermanssonResearch.Certification.Tranche9D08.raw_conflicting_orders_differ

-- SEPARATE_FINE_GRAMMAR_JOINT_ONLY_EFFECT
#check PermanssonResearch.GrammarRobust.JointOnlyCertified.original_or_joint_only
#print axioms PermanssonResearch.GrammarRobust.JointOnlyCertified.original_or_joint_only
#check PermanssonResearch.GrammarRobust.JointOnlyCertified.original_or_joint_is_minimal
#print axioms PermanssonResearch.GrammarRobust.JointOnlyCertified.original_or_joint_is_minimal
#check PermanssonResearch.GrammarRobust.JointOnlyCertified.original_and_has_two_distinct_minimal_singletons
#print axioms PermanssonResearch.GrammarRobust.JointOnlyCertified.original_and_has_two_distinct_minimal_singletons
#check PermanssonResearch.GrammarRobust.JointOnlyCertified.original_or_action_not_positive
#print axioms PermanssonResearch.GrammarRobust.JointOnlyCertified.original_or_action_not_positive


