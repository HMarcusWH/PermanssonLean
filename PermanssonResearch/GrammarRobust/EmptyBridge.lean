import PermanssonResearch.GrammarRobust.OriginalInterventionBridge
import Mathlib.Tactic

/-!
# Lane B: complete empty-block model identity

The empty component set must be *the baseline model itself*, not only an
equality of one coordinate or an equality asserted in the grammar.
-/

namespace PermanssonResearch
namespace GrammarRobust

universe uS uX uA uI uJ uC

theorem atomicBlockModel_empty
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ}
    [Fintype IA] [Fintype IU] [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU) :
    atomicBlockModel M bank ∅ = M := by
  cases M with
  | mk generator world world_isMarkov =>
    cases generator with
    | mk action update action_isMarkov update_isMarkov =>
      simp [atomicBlockModel, patchedAction, patchedUpdate,
        actionAtoms_empty, updateAtoms_empty]

theorem blockModel_empty
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (Γ : PartitionGrammar IA IU C) :
    blockModel M bank Γ ∅ = M := by
  simp [blockModel, atomicBlockModel_empty]

theorem empty_admitted_block_apply_eq
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (Γ : PartitionGrammar IA IU C) :
    (admittedBlockIntervention M bank Γ (AllowedBlock.empty Γ)).intervention.apply = M := by
  rw [admittedBlockIntervention_apply]
  exact blockModel_empty M bank Γ

end GrammarRobust
end PermanssonResearch
