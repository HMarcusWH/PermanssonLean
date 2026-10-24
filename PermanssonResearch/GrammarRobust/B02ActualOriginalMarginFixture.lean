import PermanssonResearch.GrammarRobust.BooleanMinimalityCases
import PermanssonResearch.GrammarRobust.FullRelabelingTransport
import Mathlib.Tactic

/-!
B-02 original finite uniform constitutive margin and local minimality.

Unlike Nat-order-only illustrations, the predicate is the genuine original
blockMargin of the fixed path-law property on the declared comparison set.
The relabeling comes from a real two-atom bank, nonidentity components and
an exactly identical typed strategic-world process. Coarse aggregation
does NOT inherit local minimality, by the existing B7 witness.
No unrestricted grammar/order/monotonicity inference is asserted.
-/

namespace PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.GrammarRobust
open BooleanModel BooleanBaseline BooleanOneStepEvents
open BooleanMinimalityCases RelabelingOrderWitness
open FullRelabelingTransport
open RelabelingWitness

theorem two_actual_minimal_original_blocks :
    IsMinimalAllowed fine andPos ({0} : Finset (Fin 2)) ∧
    IsMinimalAllowed fine andPos ({1} : Finset (Fin 2)) := by
  exact ⟨and_action_minimal, and_update_minimal⟩

theorem nonidentity_relabeling_preserves_actual_margin :
    0 < blockMargin baseline bank fine (fineBlock {0})
      spec (propertyAtOne andP) comparison ∧
    blockMargin baseline bank fine (fineBlock {0})
      spec (propertyAtOne andP) comparison =
    blockMargin baseline bank RelabelingWitness.relabeled
      (RelabelingOrderWitness.relabeledBlock (relabelEquiv {0}))
      spec (propertyAtOne andP) comparison := by
  constructor
  · exact andPos_action
  · exact relabeled_margin_all ({0} : Finset (Fin 2))
      (propertyAtOne andP)

theorem actual_local_minimality_transport_not_global_identity :
    (IsMinimalAllowed fine andPos ({0} : Finset (Fin 2)) ∧
     IsMinimalAllowed RelabelingWitness.relabeled relabeledAndPos
        (relabelEquiv ({0} : Finset (Fin 2)))) ∧
    relabelEquiv ({0} : Finset (Fin 2)) ≠ ({0} : Finset (Fin 2)) := by
  constructor
  · exact ⟨and_action_minimal,
      (relabeled_AND_minimal_iff ({0} : Finset (Fin 2))).mp
        and_action_minimal⟩
  · exact relabelEquiv_is_nonidentity

theorem actual_coarsening_does_not_preserve_minimality :
    IsMinimalAllowed coarse coarseAndPos ({0} : Finset (Fin 1)) ∧
    ¬ IsMinimalAllowed fine andPos
      (coarsening.lift ({0} : Finset (Fin 1))) :=
  B7_minimality_not_preserved_by_refinement

theorem and_joint_is_positive_but_not_minimal :
    andPos ({0,1} : Finset (Fin 2)) ∧
    ¬ IsMinimalAllowed fine andPos ({0,1} : Finset (Fin 2)) :=
  ⟨andPos_joint, and_joint_not_minimal⟩

end PermanssonResearch.GrammarRobust.B02ActualOriginalMarginFixture
