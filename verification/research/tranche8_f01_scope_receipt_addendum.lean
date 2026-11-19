import PermanssonResearch.MultiAgent.MeasurableProductTwoMatchedExamples
import verification.research.MultiAgentFiniteProduct

/-!
# F-01 criterion and scope receipt addendum

This probe exposes named receipts for the original asymmetric player-swap
criterion, the unchanged Fin 3 protocol fixture, and the separately scoped
measurable conditional-product Fin 2 results. The original Fin 3 verification
fixture is compiled as a prerequisite and imported without changing its bytes.

The generic row equalities below explicitly exchange private mechanisms and
pull back their inputs. The Bool-private-state witness makes this observable;
the older common/world fixture alone has Unit private states. PlayerSwap's
canonical path-law theorem below retains its finite-space hypotheses. The
matched measurable Fin 2 results retain the conditional-product construction,
admitted anchors, pulled-back property and comparison-set image hypotheses.
They do not assert transport of arbitrary correlated protocols or Exact GR.
No certification acceptance decision is made by this technical evidence.
-/

open MeasureTheory ProbabilityTheory Set PermanssonLean
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum

section PrivateInputRows
variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

/-- Swapped first-player private update is the old second player's update
on the reindexed full update input. -/
theorem swapped_first_private_update_row
    (a : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (i : UpdateInput (GameState S0 S2 S1) X (A2 × A1)) :
    (PlayerSwap.first a).update i = a.update (PlayerSwap.updateInput i) := rfl

/-- Swapped second-player private update is the old first player's update
on the reindexed full update input. -/
theorem swapped_second_private_update_row
    (a : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (i : UpdateInput (GameState S0 S2 S1) X (A2 × A1)) :
    (PlayerSwap.second a).update i = a.update (PlayerSwap.updateInput i) := rfl

theorem swapped_common_update_row
    (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (i : UpdateInput (GameState S0 S2 S1) X (A2 × A1)) :
    (PlayerSwap.generator G).common i = G.common (PlayerSwap.updateInput i) := rfl

theorem swapped_physical_input_row
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X)
    (i : WorldInput (GameState S0 S2 S1) X (A2 × A1)) :
    PlayerSwap.physical P i = P (PlayerSwap.worldInput i) := rfl
end PrivateInputRows

/-- Nonconstant Bool-valued private update reading the first action. -/
noncomputable def privateFirst : PlayerOneMechanism Unit Bool Bool Bool Bool Bool where
  action := Kernel.const _ (Measure.dirac false)
  update := Kernel.deterministic (fun i => i.1.2.1) (by fun_prop)
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

/-- A distinct nonconstant private update reading the second action. -/
noncomputable def privateSecond : PlayerTwoMechanism Unit Bool Bool Bool Bool Bool where
  action := Kernel.const _ (Measure.dirac true)
  update := Kernel.deterministic (fun i => i.1.2.2) (by fun_prop)
  action_isMarkov := inferInstance
  update_isMarkov := inferInstance

def privateInput (a b : Bool) :
    UpdateInput (GameState Unit Bool Bool) Bool (Bool × Bool) :=
  (((((), (false, true)), false), (a, b)), false)

theorem private_update_inputs_are_reindexed :
    (PlayerSwap.first privateSecond).update (privateInput false true) {true} = 0 ∧
    privateSecond.update (privateInput false true) {true} = 1 ∧
    (PlayerSwap.second privateFirst).update (privateInput false true) {true} = 1 ∧
    privateFirst.update (privateInput false true) {true} = 0 := by
  simp [privateFirst, privateSecond, privateInput, PlayerSwap.first,
    PlayerSwap.second, PlayerSwap.updateInput, PlayerSwap.worldInput,
    PlayerSwap.state, PlayerSwap.strategic, Kernel.comap_apply,
    Kernel.deterministic_apply, Measure.dirac_apply]

theorem private_update_kernels_are_distinct :
    privateFirst.update ≠ privateSecond.update := by
  intro h
  have hm := congrArg
    (fun K : Kernel (UpdateInput (GameState Unit Bool Bool) Bool (Bool × Bool)) Bool =>
      K (privateInput false true) {true}) h
  simp [privateFirst, privateSecond, privateInput,
    Kernel.deterministic_apply, Measure.dirac_apply] at hm

theorem private_update_rows_are_nonconstant :
    privateFirst.update (privateInput false false) ≠
      privateFirst.update (privateInput true true) ∧
    privateSecond.update (privateInput false false) ≠
      privateSecond.update (privateInput true true) := by
  constructor <;> intro h
  · have hm := congrArg (fun μ : Measure Bool => μ {true}) h
    simp [privateFirst, privateInput, Kernel.deterministic_apply,
      Measure.dirac_apply] at hm
  · have hm := congrArg (fun μ : Measure Bool => μ {true}) h
    simp [privateSecond, privateInput, Kernel.deterministic_apply,
      Measure.dirac_apply] at hm

section OriginalThreePlayerFixture
open FiniteProductTests FiniteProduct

/-- Named version of the unchanged original Fin 3 fixture's anonymous
closed/open protocol action-row example, using its actual definitions. -/
theorem three_player_original_protocol_action_rows :
    (baseline.closedLoop 1 (component 1 true)).toGenerator.action start {clActions} = 1 ∧
    (baseline.openLoop 1 (component 1 true) opponents).toGenerator.action start {olActions} = 1 := by
  constructor
  · rw [Generator.action_atom]
    simp [Fin.prod_univ_three, baseline, Generator.closedLoop, component,
      Kernel.const_apply, Measure.dirac_apply, clActions]
  · rw [Generator.action_atom]
    simp [Fin.prod_univ_three, baseline, Generator.openLoop, opponents, component,
      Kernel.const_apply, Measure.dirac_apply, olActions]

theorem three_player_original_asymmetric_physics :
    physical (start, clActions) {true} = 0 ∧
    physical (start, olActions) {true} = 1 := by
  simp [physical, Kernel.deterministic_apply, Measure.dirac_apply, clActions, olActions]

theorem three_player_original_empty_index_rejected : ¬ Nonempty (Fin 0) :=
  FiniteProduct.no_treated_empty
end OriginalThreePlayerFixture

end PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum

-- Complete named declaration and axiom receipts, grouped by scope.

-- private_update_and_original_fin3_facts
#check PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.swapped_first_private_update_row
#print axioms PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.swapped_first_private_update_row
#check PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.swapped_second_private_update_row
#print axioms PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.swapped_second_private_update_row
#check PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.swapped_common_update_row
#print axioms PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.swapped_common_update_row
#check PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.swapped_physical_input_row
#print axioms PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.swapped_physical_input_row
#check PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.private_update_inputs_are_reindexed
#print axioms PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.private_update_inputs_are_reindexed
#check PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.private_update_kernels_are_distinct
#print axioms PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.private_update_kernels_are_distinct
#check PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.private_update_rows_are_nonconstant
#print axioms PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.private_update_rows_are_nonconstant
#check PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.three_player_original_protocol_action_rows
#print axioms PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.three_player_original_protocol_action_rows
#check PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.three_player_original_asymmetric_physics
#print axioms PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.three_player_original_asymmetric_physics
#check PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.three_player_original_empty_index_rejected
#print axioms PermanssonResearch.MultiAgent.F01ScopeReceiptAddendum.three_player_original_empty_index_rejected

-- asymmetric_original_fixture
#check PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.actual_player_action_rows
#print axioms PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.actual_player_action_rows
#check PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.real_physical_pullback_changes_asymmetric_input
#print axioms PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.real_physical_pullback_changes_asymmetric_input
#check PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.real_common_update_pullback_changes_input
#print axioms PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.real_common_update_pullback_changes_input
#check PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.asymmetric_original_path_law_transport
#print axioms PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.asymmetric_original_path_law_transport
#check PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.mixed_starts_distinct
#print axioms PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.mixed_starts_distinct
#check PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.mixed_initial_positive_each_state
#print axioms PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.mixed_initial_positive_each_state
#check PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.mixed_initial_not_point_mass
#print axioms PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.mixed_initial_not_point_mass
#check PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.asymmetric_mixed_original_path_law_transport
#print axioms PermanssonResearch.MultiAgent.AsymmetricCommonSwapFixture.asymmetric_mixed_original_path_law_transport

-- finite_player_swap
#check PermanssonResearch.MultiAgent.PlayerSwap.generator_closedLoop
#print axioms PermanssonResearch.MultiAgent.PlayerSwap.generator_closedLoop
#check PermanssonResearch.MultiAgent.PlayerSwap.generator_openLoop
#print axioms PermanssonResearch.MultiAgent.PlayerSwap.generator_openLoop
#check PermanssonResearch.MultiAgent.PlayerSwap.actual_atom
#print axioms PermanssonResearch.MultiAgent.PlayerSwap.actual_atom
#check PermanssonResearch.MultiAgent.PlayerSwap.actual_intertwines
#print axioms PermanssonResearch.MultiAgent.PlayerSwap.actual_intertwines
#check PermanssonResearch.MultiAgent.PlayerSwap.actual_pathLaw
#print axioms PermanssonResearch.MultiAgent.PlayerSwap.actual_pathLaw
#check PermanssonResearch.MultiAgent.PlayerSwap.property_value
#print axioms PermanssonResearch.MultiAgent.PlayerSwap.property_value

-- finite_index_two_reduction
#check PermanssonResearch.MultiAgent.FiniteProduct.Two.actual_atom
#print axioms PermanssonResearch.MultiAgent.FiniteProduct.Two.actual_atom
#check PermanssonResearch.MultiAgent.FiniteProduct.Two.actual_intertwines
#print axioms PermanssonResearch.MultiAgent.FiniteProduct.Two.actual_intertwines
#check PermanssonResearch.MultiAgent.FiniteProduct.Two.actual_pathLaw
#print axioms PermanssonResearch.MultiAgent.FiniteProduct.Two.actual_pathLaw

-- measurable_conditional_product_matched_protocols
#check PermanssonResearch.MultiAgent.MeasurableProduct.Two.matchedBinaryClosed_apply
#print axioms PermanssonResearch.MultiAgent.MeasurableProduct.Two.matchedBinaryClosed_apply
#check PermanssonResearch.MultiAgent.MeasurableProduct.Two.matchedBinaryOpen_apply
#print axioms PermanssonResearch.MultiAgent.MeasurableProduct.Two.matchedBinaryOpen_apply
#check PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_closed_kernel_two
#print axioms PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_closed_kernel_two
#check PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_open_kernel_two
#print axioms PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_open_kernel_two
#check PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_closed_worlds_both_frozen
#print axioms PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_closed_worlds_both_frozen
#check PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_open_worlds_both_frozen
#print axioms PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_open_worlds_both_frozen
#check PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_closed_loop_all_initial_paths
#print axioms PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_closed_loop_all_initial_paths
#check PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_open_loop_all_initial_paths
#print axioms PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_open_loop_all_initial_paths
#check PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_closed_loop_original_margin
#print axioms PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_closed_loop_original_margin
#check PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_open_loop_original_margin
#print axioms PermanssonResearch.MultiAgent.MeasurableProduct.Two.matched_open_loop_original_margin
