import PermanssonResearch.GrammarRobust.EffectTransport
import PermanssonResearch.GrammarRobust.Minimality
import Mathlib.Tactic

/-!
# Lane B — exact image-relative minimality under genuine coarsening

A many-to-one refinement preserves constitutive margins for matched blocks,
but it does not preserve global minimality amongst every fine block.
This theorem proves exactly the defensible statement: coarse minimality is
equivalent to minimality *relative to coarse-lifted fine blocks*.
The use of surjectivity in inclusion reflection is explicit.
-/

namespace PermanssonResearch
namespace GrammarRobust

universe uI uJ uF uC

theorem Coarsening.lift_ssubset_iff
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [DecidableEq IA] [DecidableEq IU]
    [Fintype Fine] [Fintype Coarse] [DecidableEq Coarse]
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse)
    (D E : Finset Coarse) :
    ρ.lift D ⊂ ρ.lift E ↔ D ⊂ E := by
  constructor
  · intro h
    obtain ⟨hsub, hne⟩ := Finset.ssubset_iff_subset_ne.mp h
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨(ρ.lift_inclusion_iff D E).1 hsub, ?_⟩
    intro heq
    apply hne
    simp [heq]
  · intro h
    obtain ⟨hsub, hne⟩ := Finset.ssubset_iff_subset_ne.mp h
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨(ρ.lift_inclusion_iff D E).2 hsub, ?_⟩
    intro heq
    apply hne
    apply Finset.Subset.antisymm
    · exact (ρ.lift_inclusion_iff D E).1 (by simp [heq])
    · exact (ρ.lift_inclusion_iff E D).1 (by simp [heq])

/-- Being minimal among the *image of the coarsening's lift*.
This is weaker than minimality amongst all admissible fine blocks. -/
def IsImageMinimal
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [Fintype Fine] [Fintype Coarse]
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse)
    (Pfine : Finset Fine → Prop)
    (D : Finset Coarse) : Prop :=
  coarse.allowed D ∧ Pfine (ρ.lift D) ∧
    ∀ E : Finset Coarse, coarse.allowed E →
      ρ.lift E ⊂ ρ.lift D → ¬ Pfine (ρ.lift E)

theorem Coarsening.minimal_iff_imageMinimal
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [DecidableEq IA] [DecidableEq IU]
    [Fintype Fine] [Fintype Coarse] [DecidableEq Coarse]
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse)
    (Pcoarse : Finset Coarse → Prop)
    (Pfine : Finset Fine → Prop)
    (htransport : ∀ D : Finset Coarse, coarse.allowed D →
      (Pcoarse D ↔ Pfine (ρ.lift D)))
    (D : Finset Coarse) :
    IsMinimalAllowed coarse Pcoarse D ↔
      IsImageMinimal ρ Pfine D := by
  constructor
  · rintro ⟨hallowed, hpositive, hminimal⟩
    refine ⟨hallowed, (htransport D hallowed).mp hpositive, ?_⟩
    intro E hE hproper hEP
    have hEproper := (ρ.lift_ssubset_iff E D).mp hproper
    exact hminimal E hE hEproper
      ((htransport E hE).mpr hEP)
  · rintro ⟨hallowed, hpositive, hminimal⟩
    refine ⟨hallowed, (htransport D hallowed).mpr hpositive, ?_⟩
    intro E hE hproper hEP
    exact hminimal E hE ((ρ.lift_ssubset_iff E D).mpr hproper)
      ((htransport E hE).mp hEP)

end GrammarRobust
end PermanssonResearch
