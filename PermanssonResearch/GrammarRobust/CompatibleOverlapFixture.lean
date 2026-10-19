import PermanssonResearch.GrammarRobust.CompatibleOverlap
import Mathlib.Probability.Kernel.Deterministic
import Mathlib.Tactic

/-!
NEXT-06 / B-01: concrete measurable *overlapping* Boolean row patches.
Compatible overlaps share the same replacement on a genuine common row;
opposing Dirac replacements on that row are incompatible and order-sensitive.
This is a test of the ORIGINAL RowPatch.Compatible and applyCompatiblePatches
APIs, not a claim that raw patch folding rejects invalid inputs by itself.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.GrammarRobust.CompatibleOverlapFixture

noncomputable def allTrue : Kernel Bool Bool :=
  Kernel.deterministic (fun _ => true) Measurable.of_discrete
noncomputable def allFalse : Kernel Bool Bool :=
  Kernel.deterministic (fun _ => false) Measurable.of_discrete

noncomputable def firstPatch : RowPatch Bool Bool where
  region := Set.univ
  measurable_region := MeasurableSet.univ
  replacement := allTrue
  replacement_isMarkov := by unfold allTrue; infer_instance

noncomputable def overlappingPatch : RowPatch Bool Bool where
  region := {false}
  measurable_region := MeasurableSet.of_discrete
  replacement := allTrue
  replacement_isMarkov := by unfold allTrue; infer_instance

noncomputable def opposingPatch : RowPatch Bool Bool where
  region := {false}
  measurable_region := MeasurableSet.of_discrete
  replacement := allFalse
  replacement_isMarkov := by unfold allFalse; infer_instance

noncomputable def base : PermanssonLean.MarkovKernelReplacement Bool Bool :=
  ⟨Kernel.id, by infer_instance⟩

/-- The masks overlap at false; the common replacement row agrees. -/
theorem overlap_is_nonempty : false ∈ firstPatch.region ∩ overlappingPatch.region := by
  simp [firstPatch, overlappingPatch]

theorem compatible_on_actual_overlap : firstPatch.Compatible overlappingPatch := by
  intro x _ _
  rfl

/-- The generic B-OVERLAP selection theorem applies to two genuinely
non-disjoint masks and returns the actual selected Markov row. -/
theorem compatible_fold_selected :
    (applyCompatiblePatches [firstPatch, overlappingPatch] base).kernel false =
      firstPatch.replacement false := by
  have hc : ∀ p ∈ [firstPatch, overlappingPatch],
      ∀ q ∈ [firstPatch, overlappingPatch], p.Compatible q := by
    intro p hp q hq
    simp only [List.mem_cons, List.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    all_goals intro x hx hy <;> rfl
  exact applyCompatiblePatches_active [firstPatch, overlappingPatch] hc base
    firstPatch (by simp) false (by simp [firstPatch])

/-- The opposite atomic outputs have different *actual* Dirac masses. -/
theorem opposing_rows_different :
    firstPatch.replacement false ≠ opposingPatch.replacement false := by
  intro he
  have hh := congrArg (fun μ : Measure Bool => μ ({true} : Set Bool)) he
  change (allTrue false) {true} = (allFalse false) {true} at hh
  simp [allTrue, allFalse, Kernel.deterministic_apply] at hh

theorem opposing_overlap_not_compatible : ¬ firstPatch.Compatible opposingPatch := by
  intro hc
  exact opposing_rows_different (hc false (by simp [firstPatch])
    (by simp [opposingPatch]))

/-- Raw fold order matters for an incompatible pair: no unsupported
commutativity conclusion is obtained from the name of the API. -/
theorem opposing_raw_folds_differ :
    (applyCompatiblePatches [firstPatch, opposingPatch] base).kernel false ≠
      (applyCompatiblePatches [opposingPatch, firstPatch] base).kernel false := by
  have hl : (applyCompatiblePatches [firstPatch, opposingPatch] base).kernel false =
      firstPatch.replacement false := by
    change (applyRowPatch firstPatch (applyRowPatch opposingPatch base)).kernel false = _
    exact applyRowPatch_selected firstPatch _ false (by simp [firstPatch])
  have hr : (applyCompatiblePatches [opposingPatch, firstPatch] base).kernel false =
      opposingPatch.replacement false := by
    change (applyRowPatch opposingPatch (applyRowPatch firstPatch base)).kernel false = _
    exact applyRowPatch_selected opposingPatch _ false (by simp [opposingPatch])
  rw [hl, hr]
  exact opposing_rows_different

end PermanssonResearch.GrammarRobust.CompatibleOverlapFixture
