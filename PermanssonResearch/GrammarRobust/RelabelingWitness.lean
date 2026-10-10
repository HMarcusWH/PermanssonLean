import PermanssonResearch.GrammarRobust.BooleanEffects
import Mathlib.Tactic

/-!
# Lane B — B12 genuine nonidentity component-index relabeling

This is an explicit second grammar (not a renaming proposition in prose).
Its two component labels are swapped, while the physical intervention atoms,
admission, world kernel and complete induced models remain the same.
It supplements, rather than replaces, the nonbijective coarsening theorem.
-/

namespace PermanssonResearch
namespace GrammarRobust
namespace RelabelingWitness

open BooleanModel BooleanDynamics

private def swapIdx : Fin 2 ≃ Fin 2 :=
  Equiv.swap (0 : Fin 2) 1

noncomputable def relabeled :
    PartitionGrammar (Fin 1) (Fin 1) (Fin 2) where
  atomsOf := fun c => fine.atomsOf (swapIdx c)
  nonempty := by
    intro c
    exact fine.nonempty (swapIdx c)
  disjoint := by
    intro c d h
    apply fine.disjoint
    exact swapIdx.injective.ne h
  cover := by
    intro a
    obtain ⟨c,hc⟩ := fine.cover a
    exact ⟨swapIdx.symm c, by simpa using hc⟩
  allowed := fun _ => True
  allowed_empty := trivial

/-- It is a genuinely nontrivial relabeling: label 0 now contains the
update atom, although fine label 0 contains the action atom. -/
theorem relabeled_zero_is_update :
    relabeled.atomsOf (0 : Fin 2) =
      fine.atomsOf (1 : Fin 2) := by
  simp [relabeled, swapIdx]

theorem relabeled_zero_not_original_zero :
    relabeled.atomsOf (0 : Fin 2) ≠
      fine.atomsOf (0 : Fin 2) := by
  intro h
  have hx : Sum.inl (0 : Fin 1) ∈
      fine.atomsOf (1 : Fin 2) := by
    rw [← relabeled_zero_is_update, h]
    simp [fine]
  simpa [fine] using hx

theorem relabeled_zero_expands_like_update :
    relabeled.expand ({0} : Finset (Fin 2)) =
      fine.expand ({1} : Finset (Fin 2)) := by
  classical
  ext a
  simp [PartitionGrammar.expand, relabeled, swapIdx]

/-- Actual full typed α/P/U model correspondence, not just an abstract
equality of a numerical property. -/
theorem relabeled_update_model_eq :
    blockModel baseline bank relabeled ({0} : Finset (Fin 2)) =
      blockModel baseline bank fine ({1} : Finset (Fin 2)) := by
  exact blockModel_eq_of_expand_eq baseline bank relabeled fine
    ({0} : Finset (Fin 2)) ({1} : Finset (Fin 2))
    relabeled_zero_expands_like_update

end RelabelingWitness
end GrammarRobust
end PermanssonResearch
