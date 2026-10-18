import PermanssonResearch.GrammarRobust.AtomicApply

/-!
# B-OVERLAP / B-ORDER: compatible overlapping row replacements

Compatibility is checked on the actual input spaces of the kernels. The update
input therefore includes the realized action and next world. No partition or
downward-closed admissibility assumption is imposed.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch.GrammarRobust

variable {I O : Type*} [MeasurableSpace I] [MeasurableSpace O]

/-- Two row replacements agree wherever both apply. -/
def RowPatch.Compatible (p q : RowPatch I O) : Prop :=
  ∀ x, x ∈ p.region → x ∈ q.region → p.replacement x = q.replacement x

theorem RowPatch.Compatible.symm {p q : RowPatch I O}
    (h : p.Compatible q) : q.Compatible p :=
  fun x hq hp => (h x hp hq).symm

/-- Fold of actual measurable Markov row replacements. Duplicates are allowed. -/
noncomputable def applyCompatiblePatches (ps : List (RowPatch I O))
    (base : PermanssonLean.MarkovKernelReplacement I O) :
    PermanssonLean.MarkovKernelReplacement I O :=
  ps.foldr applyRowPatch base

/-- Every active patch gives the same assembled row. -/
theorem applyCompatiblePatches_active
    (ps : List (RowPatch I O))
    (hcompat : ∀ p ∈ ps, ∀ q ∈ ps, p.Compatible q)
    (base : PermanssonLean.MarkovKernelReplacement I O)
    (p : RowPatch I O) (hp : p ∈ ps) (x : I) (hx : x ∈ p.region) :
    (applyCompatiblePatches ps base).kernel x = p.replacement x := by
  classical
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    by_cases hq : x ∈ q.region
    · change (applyRowPatch q (applyCompatiblePatches qs base)).kernel x = _
      rw [applyRowPatch_selected q _ x hq]
      exact hcompat q (by simp) p hp x hq hx
    · change (applyRowPatch q (applyCompatiblePatches qs base)).kernel x = _
      rw [applyRowPatch_unselected q _ x hq]
      have hp' : p ∈ qs := by
        rcases List.mem_cons.mp hp with h | h
        · subst p; exact False.elim (hq hx)
        · exact h
      exact ih (fun a ha b hb => hcompat a (by simp [ha]) b (by simp [hb])) hp'

/-- Outside all patch masks the original row remains literal. -/
theorem applyCompatiblePatches_inactive
    (ps : List (RowPatch I O))
    (base : PermanssonLean.MarkovKernelReplacement I O) (x : I)
    (hx : ∀ p ∈ ps, x ∉ p.region) :
    (applyCompatiblePatches ps base).kernel x = base.kernel x := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change (applyRowPatch p (applyCompatiblePatches ps base)).kernel x = _
    rw [applyRowPatch_unselected p _ x (hx p (by simp))]
    exact ih (fun q hq => hx q (by simp [hq]))

/-- The assembled kernel depends on membership only. This proves permutation
invariance, repeated-patch idempotence, and compatible union/composition. -/
theorem applyCompatiblePatches_eq_of_membership
    (ps qs : List (RowPatch I O))
    (hcompat : ∀ p ∈ ps, ∀ q ∈ ps, p.Compatible q)
    (hmembers : ∀ p, p ∈ ps ↔ p ∈ qs)
    (base : PermanssonLean.MarkovKernelReplacement I O) :
    (applyCompatiblePatches ps base).kernel =
      (applyCompatiblePatches qs base).kernel := by
  classical
  have hqcompat : ∀ p ∈ qs, ∀ q ∈ qs, p.Compatible q :=
    fun p hp q hq => hcompat p ((hmembers p).mpr hp) q ((hmembers q).mpr hq)
  ext x E
  by_cases h : ∃ p ∈ ps, x ∈ p.region
  · obtain ⟨p, hp, hx⟩ := h
    rw [applyCompatiblePatches_active ps hcompat base p hp x hx,
      applyCompatiblePatches_active qs hqcompat base p ((hmembers p).mp hp) x hx]
  · have hn : ∀ p ∈ ps, x ∉ p.region := by
      intro p hp hx; exact h ⟨p, hp, hx⟩
    rw [applyCompatiblePatches_inactive ps base x hn,
      applyCompatiblePatches_inactive qs base x
        (fun p hp => hn p ((hmembers p).mpr hp))]

theorem applyCompatiblePatches_perm
    (ps qs : List (RowPatch I O))
    (hcompat : ∀ p ∈ ps, ∀ q ∈ ps, p.Compatible q)
    (hperm : ps.Perm qs)
    (base : PermanssonLean.MarkovKernelReplacement I O) :
    (applyCompatiblePatches ps base).kernel =
      (applyCompatiblePatches qs base).kernel :=
  applyCompatiblePatches_eq_of_membership ps qs hcompat (fun _ => hperm.mem_iff) base

/-- No compatibility assumption is needed to repeat a single patch. -/
theorem applyRowPatch_idempotent (p : RowPatch I O)
    (base : PermanssonLean.MarkovKernelReplacement I O) :
    (applyRowPatch p (applyRowPatch p base)).kernel = (applyRowPatch p base).kernel := by
  classical
  ext x E
  by_cases hx : x ∈ p.region
  · rw [applyRowPatch_selected p _ x hx, applyRowPatch_selected p _ x hx]
  · rw [applyRowPatch_unselected p _ x hx]

end PermanssonResearch.GrammarRobust
