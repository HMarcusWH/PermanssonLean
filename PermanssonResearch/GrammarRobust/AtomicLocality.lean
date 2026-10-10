import PermanssonResearch.GrammarRobust.BlockModels
import Mathlib.Tactic

/-!
# Lane B — proof of unaffected-row locality

This theorem is about the *actual constructed whole Markov kernels*.
A masked row not covered by any selected physical patch retains the baseline
measure, even when other rows are modified by other atoms.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust

universe uI

theorem foldlRowPatches_unaffected
    {Input Output : Type*}
    [MeasurableSpace Input] [MeasurableSpace Output]
    {I : Type uI}
    (patch : I → RowPatch Input Output)
    (rows : List I)
    (initial : PermanssonLean.MarkovKernelReplacement Input Output)
    (x : Input)
    (h : ∀ i ∈ rows, x ∉ (patch i).region) :
    (rows.foldl (fun κ i => applyRowPatch (patch i) κ) initial).kernel x =
      initial.kernel x := by
  induction rows generalizing initial with
  | nil => rfl
  | cons i rest ih =>
    have hi : x ∉ (patch i).region := h i (by simp)
    have hrest : ∀ j ∈ rest, x ∉ (patch j).region := by
      intro j hj
      exact h j (by simp [hj])
    calc
      ((i :: rest).foldl (fun κ j => applyRowPatch (patch j) κ) initial).kernel x =
          (applyRowPatch (patch i) initial).kernel x := by
            simpa [List.foldl_cons] using
              ih (applyRowPatch (patch i) initial) hrest
      _ = initial.kernel x := applyRowPatch_unselected (patch i) initial x hi

theorem patchedAction_unaffected
    {S X A : Type*}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type*}
    [LinearOrder IA]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (selected : Finset IA)
    (y : PermanssonLean.JointState S X)
    (h : ∀ i ∈ selected, y ∉ (bank.action i).region) :
    (patchedAction M bank selected).kernel y = M.generator.action y := by
  unfold patchedAction
  apply foldlRowPatches_unaffected
  intro i hi
  exact h i ((Finset.mem_sort (r := (· ≤ ·))).mp hi)

theorem patchedUpdate_unaffected
    {S X A : Type*}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type*} {IU : Type uI}
    [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (selected : Finset IU)
    (y : PermanssonLean.UpdateInput S X A)
    (h : ∀ i ∈ selected, y ∉ (bank.update i).region) :
    (patchedUpdate M bank selected).kernel y = M.generator.update y := by
  unfold patchedUpdate
  apply foldlRowPatches_unaffected
  intro i hi
  exact h i ((Finset.mem_sort (r := (· ≤ ·))).mp hi)

end GrammarRobust
end PermanssonResearch
