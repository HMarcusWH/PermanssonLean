import PermanssonResearch.GrammarRobust.CompatibleOverlap
import Mathlib.Tactic

/-!
NEXT-06 / B-01 — actual two-row compatible and conflicting overlap.

A compatible overlap acts on the real marked input true and yields the same
row irrespective of fold order. A conflicting overlap changes the assembled
Markov kernel when priority is reversed.
-/

open MeasureTheory ProbabilityTheory Set

namespace PermanssonResearch.GrammarRobust.BooleanOverlapFixture

noncomputable def alwaysFalse : Kernel Bool Bool :=
  Kernel.deterministic (fun _ : Bool => false) Measurable.of_discrete

noncomputable def alwaysTrue : Kernel Bool Bool :=
  Kernel.deterministic (fun _ : Bool => true) Measurable.of_discrete

instance : IsMarkovKernel alwaysFalse := by
  unfold alwaysFalse
  infer_instance

instance : IsMarkovKernel alwaysTrue := by
  unfold alwaysTrue
  infer_instance

noncomputable def selectedFalse : RowPatch Bool Bool where
  region := {true}
  measurable_region := MeasurableSet.of_discrete
  replacement := alwaysFalse
  replacement_isMarkov := inferInstance

noncomputable def wideFalse : RowPatch Bool Bool where
  region := Set.univ
  measurable_region := MeasurableSet.univ
  replacement := alwaysFalse
  replacement_isMarkov := inferInstance

noncomputable def selectedTrue : RowPatch Bool Bool where
  region := {true}
  measurable_region := MeasurableSet.of_discrete
  replacement := alwaysTrue
  replacement_isMarkov := inferInstance

noncomputable def base : PermanssonLean.MarkovKernelReplacement Bool Bool :=
  ⟨alwaysFalse, inferInstance⟩

theorem true_is_a_real_overlap :
    true ∈ selectedFalse.region ∧ true ∈ wideFalse.region := by
  simp [selectedFalse, wideFalse]

theorem genuinely_compatible :
    selectedFalse.Compatible wideFalse := by
  intro x hx hy
  rfl

theorem compatible_order_independent :
    (applyCompatiblePatches [selectedFalse, wideFalse] base).kernel =
      (applyCompatiblePatches [wideFalse, selectedFalse] base).kernel := by
  classical
  have hc : ∀ p ∈ [selectedFalse, wideFalse], ∀ q ∈ [selectedFalse, wideFalse],
      p.Compatible q := by
    intro p hp q hq
    simp at hp hq
    rcases hp with rfl | rfl
    · rcases hq with rfl | rfl
      · intro x hx hy; rfl
      · exact genuinely_compatible
    · rcases hq with rfl | rfl
      · exact genuinely_compatible.symm
      · intro x hx hy; rfl
  have hm : ∀ p : RowPatch Bool Bool,
      p ∈ [selectedFalse, wideFalse] ↔ p ∈ [wideFalse, selectedFalse] := by
    intro p
    simp only [List.mem_cons, List.mem_singleton]
    tauto
  exact applyCompatiblePatches_eq_of_membership _ _ hc hm base

theorem genuinely_incompatible :
    ¬ selectedFalse.Compatible selectedTrue := by
  intro hc
  have rowEq := hc true (by simp [selectedFalse]) (by simp [selectedTrue])
  have hmass := congrArg (fun μ : Measure Bool => μ {true}) rowEq
  simp [selectedFalse, selectedTrue, alwaysFalse, alwaysTrue,
    Kernel.deterministic_apply] at hmass

theorem selectedFalse_first :
    (applyCompatiblePatches [selectedFalse, selectedTrue] base).kernel true =
      alwaysFalse true := by
  change (applyRowPatch selectedFalse (applyRowPatch selectedTrue base)).kernel true = _
  exact applyRowPatch_selected selectedFalse _ true (by simp [selectedFalse])

theorem selectedTrue_first :
    (applyCompatiblePatches [selectedTrue, selectedFalse] base).kernel true =
      alwaysTrue true := by
  change (applyRowPatch selectedTrue (applyRowPatch selectedFalse base)).kernel true = _
  exact applyRowPatch_selected selectedTrue _ true (by simp [selectedTrue])

theorem incompatible_order_changes_actual_kernel :
    (applyCompatiblePatches [selectedFalse, selectedTrue] base).kernel true ≠
      (applyCompatiblePatches [selectedTrue, selectedFalse] base).kernel true := by
  intro heq
  rw [selectedFalse_first, selectedTrue_first] at heq
  have hmass := congrArg (fun μ : Measure Bool => μ {true}) heq
  simp [alwaysFalse, alwaysTrue, Kernel.deterministic_apply] at hmass

end PermanssonResearch.GrammarRobust.BooleanOverlapFixture
