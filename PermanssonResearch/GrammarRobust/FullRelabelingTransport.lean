import PermanssonResearch.GrammarRobust.RelabelingOrderWitness
import PermanssonResearch.GrammarRobust.IsomorphicTransport
import Mathlib.Tactic

/-!
# Lane B — substantive all-block positive order-isomorphic grammar transport

Unlike a theorem merely assuming matching constitutive effects or a single
selected component, the same *frozen physical bank* constructs both grammars.
This file proves for EVERY subset D of the two components:
  (1) the component relabeling is a genuine nonidentity order isomorphism;
  (2) the selected atom sets and the complete strategic α/P/U models agree;
  (3) original canonical path-law effects and uniform margins agree;
  (4) uniform constitutive classification agrees;
  (5) original global minimality is preserved and reflected.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace GrammarRobust
namespace FullRelabelingTransport

open PermanssonLean PermanssonLean.RegimeSpecification
open BooleanModel BooleanBaseline BooleanDynamics BooleanPersistence
open BooleanOneStepEvents BooleanEffects BooleanMinimalityCases
open RelabelingWitness RelabelingOrderWitness

private theorem relabeled_atoms_swap (c : Fin 2) :
    relabeled.atomsOf (swapIdx c) = fine.atomsOf c := by
  fin_cases c <;> simp [relabeled, swapIdx]

theorem relabeled_expand_all (D : Finset (Fin 2)) :
    relabeled.expand (renameBlock D) = fine.expand D := by
  classical
  ext a
  simp only [PartitionGrammar.expand, Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, ha⟩
    change c ∈ D.image swapIdx at hc
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
    refine ⟨b, hb, ?_⟩
    simpa only [relabeled_atoms_swap] using ha
  · rintro ⟨b, hb, ha⟩
    refine ⟨swapIdx b, ?_, ?_⟩
    · change swapIdx b ∈ D.image swapIdx
      exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    · simpa only [relabeled_atoms_swap] using ha

theorem relabeled_model_all (D : Finset (Fin 2)) :
    blockModel baseline bank relabeled (renameBlock D) =
      blockModel baseline bank fine D :=
  blockModel_eq_of_expand_eq baseline bank relabeled fine
    (renameBlock D) D (relabeled_expand_all D)

def relabelEquiv : Finset (Fin 2) ≃ Finset (Fin 2) :=
  swapIdx.finsetCongr

theorem relabelEquiv_apply (D : Finset (Fin 2)) :
    relabelEquiv D = renameBlock D := by
  classical
  change D.map swapIdx.toEmbedding = D.image swapIdx
  exact Finset.map_eq_image

theorem relabelEquiv_is_nonidentity :
    relabelEquiv ({0} : Finset (Fin 2)) ≠ ({0} : Finset (Fin 2)) := by
  rw [relabelEquiv_apply, renameBlock_zero_is_one]
  decide

theorem relabelEquiv_order_iff (D E : Finset (Fin 2)) :
    D ⊂ E ↔ relabelEquiv D ⊂ relabelEquiv E := by
  rw [relabelEquiv_apply, relabelEquiv_apply]
  exact renameBlock_order_iff D E

theorem relabeled_effect_all (D : Finset (Fin 2))
    (ψ : RegimePropertyMap Y ℝ) (y : Y) :
    blockEffect baseline bank fine (fineBlock D) ψ y =
      blockEffect baseline bank relabeled
        (relabeledBlock (relabelEquiv D)) ψ y := by
  unfold blockEffect constitutiveEffect intervenedPropertyValue
  rw [admittedBlockIntervention_apply, admittedBlockIntervention_apply]
  rw [relabelEquiv_apply, relabeled_model_all]

theorem relabeled_margin_all (D : Finset (Fin 2))
    (ψ : RegimePropertyMap Y ℝ) :
    blockMargin baseline bank fine (fineBlock D) spec ψ comparison =
      blockMargin baseline bank relabeled
        (relabeledBlock (relabelEquiv D)) spec ψ comparison := by
  unfold blockMargin constitutiveMargin
  apply congrArg sInf
  apply Set.image_congr
  intro y _
  exact relabeled_effect_all D ψ y

theorem relabeled_uniform_all (D : Finset (Fin 2))
    (ψ : RegimePropertyMap Y ℝ) :
    IsUniformBlock baseline bank fine (fineBlock D) spec ψ comparison ↔
      IsUniformBlock baseline bank relabeled
        (relabeledBlock (relabelEquiv D)) spec ψ comparison := by
  change 0 < blockMargin baseline bank fine (fineBlock D) spec ψ comparison ↔
    0 < blockMargin baseline bank relabeled
      (relabeledBlock (relabelEquiv D)) spec ψ comparison
  rw [relabeled_margin_all D ψ]

theorem relabeled_AND_minimal_iff (D : Finset (Fin 2)) :
    IsMinimalAllowed fine andPos D ↔
      IsMinimalAllowed relabeled relabeledAndPos (relabelEquiv D) := by
  apply minimalAllowed_iff_of_blockOrderEquiv
    fine relabeled andPos relabeledAndPos relabelEquiv
  · intro E
    simp [fine, relabeled]
  · intro E
    exact relabeled_uniform_all E (propertyAtOne andP)
  · intro E F
    exact relabelEquiv_order_iff E F

end FullRelabelingTransport
end GrammarRobust
end PermanssonResearch
