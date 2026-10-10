import PermanssonResearch.GrammarRobust.OriginalInterventionBridge

/-!
# Lane B — genuine many-to-one component coarsening

A physical atom bank is fixed.  Two partitions assign its atoms to different
semantic components.  A surjective map sends each fine component to one
coarse component, whose atom set is precisely the union of its preimage.
The expansion theorem is derived from that partition equation.
-/

namespace PermanssonResearch
namespace GrammarRobust

universe uI uJ uF uC

structure Coarsening
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [Fintype Fine] [Fintype Coarse]
    [DecidableEq Coarse]
    (fine : PartitionGrammar IA IU Fine)
    (coarse : PartitionGrammar IA IU Coarse) where
  map : Fine → Coarse
  onto : Function.Surjective map
  coarse_atoms : ∀ c : Coarse,
    coarse.atomsOf c =
      (Finset.univ.filter (fun f : Fine => map f = c)).biUnion fine.atomsOf
  respects_allowed : ∀ D : Finset Coarse, coarse.allowed D →
    fine.allowed (Finset.univ.filter (fun f : Fine => map f ∈ D))

noncomputable def Coarsening.lift
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [Fintype Fine] [Fintype Coarse]
    [DecidableEq Coarse]
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse)
    (D : Finset Coarse) : Finset Fine := by
  classical
  exact Finset.univ.filter (fun f => ρ.map f ∈ D)

theorem Coarsening.expand_lift
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [Fintype Fine] [Fintype Coarse]
    [DecidableEq Coarse]
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse)
    (D : Finset Coarse) :
    fine.expand (ρ.lift D) = coarse.expand D := by
  classical
  ext a
  simp only [PartitionGrammar.expand, Finset.mem_biUnion]
  constructor
  · rintro ⟨f, hf, ha⟩
    have hD : ρ.map f ∈ D := by
      simpa [Coarsening.lift] using hf
    refine ⟨ρ.map f, hD, ?_⟩
    rw [ρ.coarse_atoms]
    have hfilt : f ∈ Finset.univ.filter
        (fun q : Fine => ρ.map q = ρ.map f) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨f, hfilt, ha⟩
  · rintro ⟨c, hc, ha⟩
    rw [ρ.coarse_atoms] at ha
    rcases Finset.mem_biUnion.mp ha with ⟨f, hf, hfa⟩
    have hfc : ρ.map f = c := by simpa using hf
    refine ⟨f, ?_, hfa⟩
    simp [Coarsening.lift, hfc, hc]

theorem Coarsening.lift_inclusion_iff
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [Fintype Fine] [Fintype Coarse]
    [DecidableEq Coarse]
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse)
    (D E : Finset Coarse) :
    ρ.lift D ⊆ ρ.lift E ↔ D ⊆ E := by
  classical
  constructor
  · intro h c hc
    obtain ⟨f, hf⟩ := ρ.onto c
    have hfl : f ∈ ρ.lift D := by simp [Coarsening.lift, hf, hc]
    have hfe := h hfl
    simpa [Coarsening.lift, hf] using hfe
  · intro h f hf
    have hm : ρ.map f ∈ D := by simpa [Coarsening.lift] using hf
    simp [Coarsening.lift, h hm]

end GrammarRobust
end PermanssonResearch
