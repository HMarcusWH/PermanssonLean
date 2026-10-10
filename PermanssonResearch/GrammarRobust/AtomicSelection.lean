import PermanssonResearch.GrammarRobust.AtomicLocality
import Mathlib.Tactic

/-!
# Lane B: selected-row locality and permutation-independent semantics

Disjointness and a no-duplicate enumeration make the selected physical atom
unique at every input row. A selected row is assigned its frozen replacement,
and unselected rows retain the baseline kernel.
-/

open ProbabilityTheory MeasureTheory
namespace PermanssonResearch
namespace GrammarRobust

universe uI

theorem foldlRowPatches_selected
    {Input Output : Type*}
    [MeasurableSpace Input] [MeasurableSpace Output]
    {I : Type uI}
    (patch : I → RowPatch Input Output)
    (rows : List I)
    (initial : PermanssonLean.MarkovKernelReplacement Input Output)
    (hnodup : rows.Nodup)
    (hdisj : ∀ i ∈ rows, ∀ j ∈ rows, i ≠ j →
      Disjoint (patch i).region (patch j).region)
    (i : I) (hi : i ∈ rows) (x : Input)
    (hx : x ∈ (patch i).region) :
    (rows.foldl (fun κ j => applyRowPatch (patch j) κ) initial).kernel x =
      (patch i).replacement x := by
  induction rows generalizing initial with
  | nil =>
      simp at hi
  | cons j rest ih =>
      have hrestnodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hnot : j ∉ rest := (List.nodup_cons.mp hnodup).1
      have hsub : ∀ a ∈ rest, ∀ b ∈ rest, a ≠ b →
          Disjoint (patch a).region (patch b).region := by
        intro a ha b hb hab
        exact hdisj a (by simp [ha]) b (by simp [hb]) hab
      by_cases hji : j = i
      · subst j
        have hrest : ∀ k ∈ rest, x ∉ (patch k).region := by
          intro k hk hkx
          have hik : i ≠ k := by
            intro heq
            exact hnot (heq ▸ hk)
          have hd := hdisj i (by simp) k (by simp [hk]) hik
          exact (Set.disjoint_left.mp hd) hx hkx
        simp only [List.foldl_cons]
        rw [foldlRowPatches_unaffected patch rest
          (applyRowPatch (patch i) initial) x hrest]
        exact applyRowPatch_selected (patch i) initial x hx
      · have hii : i ∈ rest := by
          rcases List.mem_cons.mp hi with h | h
          · exact False.elim (hji h.symm)
          · exact h
        simpa only [List.foldl_cons] using
          ih (applyRowPatch (patch j) initial) hrestnodup hsub hii

/-- A physical patch list has identical output at any selected row, no
matter which order the physical components were enumerated in. -/
theorem foldlRowPatches_eq_of_mem_iff
    {Input Output : Type*}
    [MeasurableSpace Input] [MeasurableSpace Output]
    {I : Type uI}
    (patch : I → RowPatch Input Output)
    (rows₁ rows₂ : List I)
    (initial : PermanssonLean.MarkovKernelReplacement Input Output)
    (hmem : ∀ i, i ∈ rows₁ ↔ i ∈ rows₂)
    (hnd₁ : rows₁.Nodup) (hnd₂ : rows₂.Nodup)
    (hdisj : ∀ i j : I, i ≠ j →
      Disjoint (patch i).region (patch j).region) :
    (rows₁.foldl (fun κ j => applyRowPatch (patch j) κ) initial).kernel =
    (rows₂.foldl (fun κ j => applyRowPatch (patch j) κ) initial).kernel := by
  apply Kernel.ext
  intro x
  by_cases hhit : ∃ i ∈ rows₁, x ∈ (patch i).region
  · obtain ⟨i, hi, hx⟩ := hhit
    have hdisj₁ : ∀ i ∈ rows₁, ∀ j ∈ rows₁, i ≠ j →
        Disjoint (patch i).region (patch j).region := by
      intro a _ b _ hab
      exact hdisj a b hab
    have hdisj₂ : ∀ i ∈ rows₂, ∀ j ∈ rows₂, i ≠ j →
        Disjoint (patch i).region (patch j).region := by
      intro a _ b _ hab
      exact hdisj a b hab
    rw [foldlRowPatches_selected patch rows₁ initial hnd₁ hdisj₁ i hi x hx]
    exact (foldlRowPatches_selected patch rows₂ initial hnd₂ hdisj₂
      i ((hmem i).mp hi) x hx).symm
  · have h₁ : ∀ i ∈ rows₁, x ∉ (patch i).region := by
      intro i hi hx
      exact hhit ⟨i, hi, hx⟩
    have h₂ : ∀ i ∈ rows₂, x ∉ (patch i).region := by
      intro i hi hx
      exact hhit ⟨i, (hmem i).mpr hi, hx⟩
    rw [foldlRowPatches_unaffected patch rows₁ initial x h₁,
      foldlRowPatches_unaffected patch rows₂ initial x h₂]

end GrammarRobust
end PermanssonResearch
