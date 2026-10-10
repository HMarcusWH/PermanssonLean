import PermanssonResearch.GrammarRobust.RelabelingWitness
import PermanssonResearch.GrammarRobust.BooleanMinimalityCases
import Mathlib.Tactic

/-!
# Lane B B12 — positive full-order relabeling and actual minimality certificate

There are two differently indexed component grammars over the same physical
alpha/update atom bank. Component label 0 becomes the update atom instead
of the action atom. The induced kernel is unchanged when matching each
finite component block through the explicit nonidentity permutation.
Unlike B5's arbitrary block-label permutation, this map is induced by an
actual component permutation and preserves proper-subblock inclusion.
-/

namespace PermanssonResearch
namespace GrammarRobust
namespace RelabelingOrderWitness

open PermanssonLean PermanssonLean.RegimeSpecification
open BooleanModel BooleanBaseline BooleanDynamics BooleanPersistence
open BooleanOneStepEvents BooleanEffects
open BooleanMinimalityCases RelabelingWitness

private def swapComponents : Fin 2 ≃ Fin 2 :=
  Equiv.swap (0 : Fin 2) 1

def renameBlock : Finset (Fin 2) ≃ Finset (Fin 2) :=
  swapComponents.finsetCongr

/-- Genuine componentwise relabeling preserves *and reflects* all
proper-subblock order relations, unlike an arbitrary block-label bijection. -/
theorem renameBlock_order_iff (D E : Finset (Fin 2)) :
    D ⊂ E ↔ renameBlock D ⊂ renameBlock E := by
  classical
  change D ⊂ E ↔ D.image swapComponents ⊂ E.image swapComponents
  exact (Finset.image_ssubset_image swapComponents.injective).symm

private theorem renamed_component_atoms (c : Fin 2) :
    relabeled.atomsOf (swapComponents c) = fine.atomsOf c := by
  fin_cases c <;> simp [relabeled, swapComponents]

/-- Every real block, not only one singleton, selects exactly the same
physical atoms after the nonidentity relabeling. -/
theorem renameBlock_expansion (D : Finset (Fin 2)) :
    relabeled.expand (renameBlock D) = fine.expand D := by
  classical
  ext a
  simp only [PartitionGrammar.expand, Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, ha⟩
    have hc' : c ∈ D.image swapComponents := by
      simpa [renameBlock, Equiv.finsetCongr_apply] using hc
    obtain ⟨b,hb,hbc⟩ := Finset.mem_image.mp hc'
    subst c
    refine ⟨b, hb, ?_⟩
    simpa [renamed_component_atoms] using ha
  · rintro ⟨b,hb,ha⟩
    refine ⟨swapComponents b, ?_, ?_⟩
    · change swapComponents b ∈ D.image swapComponents
      exact Finset.mem_image.mpr ⟨b,hb,rfl⟩
    · simpa [renamed_component_atoms] using ha

/-- Actual process conservation for *every* finite intervention block
under a valid component permutation. -/
theorem renameBlock_model_transport (D : Finset (Fin 2)) :
    blockModel baseline bank relabeled (renameBlock D) =
      blockModel baseline bank fine D := by
  exact blockModel_eq_of_expand_eq baseline bank relabeled fine
    (renameBlock D) D (renameBlock_expansion D)

noncomputable def relabeledBlock (D : Finset (Fin 2)) :
    AllowedBlock relabeled := ⟨D, trivial⟩

def relabeledAndPos (D : Finset (Fin 2)) : Prop :=
  IsUniformBlock baseline bank relabeled (relabeledBlock D)
    spec (propertyAtOne andP) comparison

/-- Proved positive margin for the relabeled component 0, computed from
the same canonical AND path-law property as the original fine grammar. -/
theorem relabeled_zero_AND_margin_one :
    blockMargin baseline bank relabeled (relabeledBlock {0}) spec
      (propertyAtOne andP) comparison = 1 := by
  apply blockMargin_eq_of_constant_effect
  intro y _
  have hv := and_update_one y
  unfold blockEffect constitutiveEffect at hv ⊢
  unfold baselinePropertyValue intervenedPropertyValue at hv ⊢
  rw [admittedBlockIntervention_apply] at hv ⊢
  rw [relabeled_update_model_eq]
  exact hv

theorem relabeled_empty_margin_zero :
    blockMargin baseline bank relabeled (relabeledBlock ∅) spec
      (propertyAtOne andP) comparison = 0 := by
  apply blockMargin_eq_of_constant_effect
  intro y _
  unfold blockEffect constitutiveEffect
  unfold baselinePropertyValue intervenedPropertyValue
  rw [admittedBlockIntervention_apply, blockModel_empty]
  simp

theorem relabeled_zero_AND_minimal :
    IsMinimalAllowed relabeled relabeledAndPos
      ({0} : Finset (Fin 2)) := by
  refine ⟨trivial, ?_, ?_⟩
  · change 0 < blockMargin baseline bank relabeled
      (relabeledBlock {0}) spec (propertyAtOne andP) comparison
    rw [relabeled_zero_AND_margin_one]
    norm_num
  · intro E _ hproper hpositive
    have heq : E = ∅ := Finset.eq_empty_of_ssubset_singleton hproper
    change 0 < blockMargin baseline bank relabeled
      (relabeledBlock E) spec (propertyAtOne andP) comparison at hpositive
    rw [heq, relabeled_empty_margin_zero] at hpositive
    norm_num at hpositive

end RelabelingOrderWitness
end GrammarRobust
end PermanssonResearch
