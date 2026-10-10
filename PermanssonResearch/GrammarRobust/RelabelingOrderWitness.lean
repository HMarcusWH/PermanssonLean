import PermanssonResearch.GrammarRobust.RelabelingWitness
import PermanssonResearch.GrammarRobust.BooleanMinimalityCases
import Mathlib.Tactic

/-!
# Lane B B12 — an actual nonidentity order-preserving component relabeling

Component indices 0 and 1 are swapped. At the primitive level the new
component 0 selects exactly the old update atom and yields the identical
full typed α/P/U model, while the swapped component map preserves and
reflects proper inclusion for ALL finite semantic blocks. The AND
constitutive margin makes the new component 0 concretely minimal.
This is distinct from an arbitrary block-label swap (B5).
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust
namespace RelabelingOrderWitness

open PermanssonLean PermanssonLean.RegimeSpecification
open BooleanModel BooleanBaseline BooleanDynamics BooleanPersistence
open BooleanOneStepEvents BooleanEffects
open BooleanMinimalityCases RelabelingWitness

def renameBlock (D : Finset (Fin 2)) : Finset (Fin 2) :=
  D.image (Equiv.swap (0 : Fin 2) 1)

theorem renameBlock_order_iff (D E : Finset (Fin 2)) :
    D ⊂ E ↔ renameBlock D ⊂ renameBlock E := by
  exact (Finset.image_ssubset_image
    (Equiv.swap (0 : Fin 2) 1).injective).symm

theorem renameBlock_zero_is_one :
    renameBlock ({0} : Finset (Fin 2)) =
      ({1} : Finset (Fin 2)) := by
  simp [renameBlock]

/-- The concrete new component zero is genuinely the old component one;
the full process, not just its numerical outcome, is transported. -/
theorem relabeled_zero_model_eq_original_update :
    blockModel baseline bank relabeled ({0} : Finset (Fin 2)) =
      blockModel baseline bank fine updateOnly := by
  exact relabeled_update_model_eq

noncomputable def relabeledBlock (D : Finset (Fin 2)) :
    AllowedBlock relabeled := ⟨D, trivial⟩

def relabeledAndPos (D : Finset (Fin 2)) : Prop :=
  IsUniformBlock baseline bank relabeled (relabeledBlock D)
    spec (propertyAtOne andP) comparison

theorem relabeled_zero_AND_margin_one :
    blockMargin baseline bank relabeled (relabeledBlock {0}) spec
      (propertyAtOne andP) comparison = 1 := by
  apply blockMargin_eq_of_constant_effect
  intro y _
  have hv := and_update_one y
  unfold blockEffect constitutiveEffect at hv ⊢
  unfold baselinePropertyValue intervenedPropertyValue at hv ⊢
  rw [admittedBlockIntervention_apply] at hv ⊢
  change dist
    (propertyAtOne andP (pathProbability baseline (diracProba y)))
    (propertyAtOne andP
      (pathProbability (blockModel baseline bank fine updateOnly)
        (diracProba y))) = 1 at hv
  change dist
    (propertyAtOne andP (pathProbability baseline (diracProba y)))
    (propertyAtOne andP
      (pathProbability (blockModel baseline bank relabeled {0})
        (diracProba y))) = 1
  rw [relabeled_update_model_eq]
  exact hv

theorem relabeled_empty_AND_margin_zero :
    blockMargin baseline bank relabeled (relabeledBlock ∅) spec
      (propertyAtOne andP) comparison = 0 := by
  apply blockMargin_eq_of_constant_effect
  intro y _
  unfold blockEffect constitutiveEffect
  unfold baselinePropertyValue intervenedPropertyValue
  rw [admittedBlockIntervention_apply]
  change dist
    (propertyAtOne andP (pathProbability baseline (diracProba y)))
    (propertyAtOne andP
      (pathProbability (blockModel baseline bank relabeled ∅)
        (diracProba y))) = 0
  rw [blockModel_empty]
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
    rw [heq, relabeled_empty_AND_margin_zero] at hpositive
    norm_num at hpositive

end RelabelingOrderWitness
end GrammarRobust
end PermanssonResearch
