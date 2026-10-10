import PermanssonResearch.GrammarRobust.EmptyBridge
import Mathlib.Tactic

/-!
# Lane B — singleton physical atom as an original typed intervention

The bridge is not an assertion that every component has a unique physical
meaning. For a one-atom block, the *actual model* constructed by the new
grammar equals the original typed `.actionSelection` or `.strategicUpdate`
replacement, with the other strategic primitive and P unchanged.
-/

namespace PermanssonResearch
namespace GrammarRobust

universe uS uX uA uI uJ

@[simp] theorem actionAtoms_singleton_inl
    {IA : Type uI} {IU : Type uJ}
    [Fintype IA] (i : IA) :
    actionAtoms (IA := IA) (IU := IU) ({Sum.inl i} : Finset (Atom IA IU)) =
      {i} := by
  classical
  ext j
  simp [actionAtoms]

@[simp] theorem updateAtoms_singleton_inl
    {IA : Type uI} {IU : Type uJ}
    [Fintype IU] (i : IA) :
    updateAtoms (IA := IA) (IU := IU) ({Sum.inl i} : Finset (Atom IA IU)) =
      ∅ := by
  classical
  ext j
  simp [updateAtoms]

@[simp] theorem actionAtoms_singleton_inr
    {IA : Type uI} {IU : Type uJ}
    [Fintype IA] (j : IU) :
    actionAtoms (IA := IA) (IU := IU) ({Sum.inr j} : Finset (Atom IA IU)) =
      ∅ := by
  classical
  ext i
  simp [actionAtoms]

@[simp] theorem updateAtoms_singleton_inr
    {IA : Type uI} {IU : Type uJ}
    [Fintype IU] (j : IU) :
    updateAtoms (IA := IA) (IU := IU) ({Sum.inr j} : Finset (Atom IA IU)) =
      {j} := by
  classical
  ext i
  simp [updateAtoms]

theorem atomicBlockModel_singleton_action
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ}
    [Fintype IA] [Fintype IU] [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU) (i : IA) :
    atomicBlockModel M bank ({Sum.inl i} : Finset (Atom IA IU)) =
      PermanssonLean.applyReplacement M .actionSelection
        (patchedAction M bank {i}) := by
  cases M with
  | mk generator world world_isMarkov =>
    cases generator with
    | mk action update action_isMarkov update_isMarkov =>
      simp [atomicBlockModel, PermanssonLean.applyReplacement,
        patchedUpdate, updateAtoms_singleton_inl]

theorem atomicBlockModel_singleton_update
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ}
    [Fintype IA] [Fintype IU] [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU) (j : IU) :
    atomicBlockModel M bank ({Sum.inr j} : Finset (Atom IA IU)) =
      PermanssonLean.applyReplacement M .strategicUpdate
        (patchedUpdate M bank {j}) := by
  cases M with
  | mk generator world world_isMarkov =>
    cases generator with
    | mk action update action_isMarkov update_isMarkov =>
      simp [atomicBlockModel, PermanssonLean.applyReplacement,
        patchedAction, actionAtoms_singleton_inr]

end GrammarRobust
end PermanssonResearch
