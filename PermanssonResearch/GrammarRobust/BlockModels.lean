import PermanssonResearch.GrammarRobust.PartitionGrammar

/-!
# Lane B — complete constructed strategic-world models for blocks

No post-intervention world or induced kernel is a free field.
The model's α and U are built from the common physical atoms; P is copied
definitionally from the frozen baseline.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust

universe uS uX uA uI uJ uC

noncomputable def actionAtoms
    {IA : Type uI} {IU : Type uJ} [Fintype IA]
    (E : Finset (Atom IA IU)) : Finset IA := by
  classical
  exact Finset.univ.filter (fun i => Sum.inl i ∈ E)

noncomputable def updateAtoms
    {IA : Type uI} {IU : Type uJ} [Fintype IU]
    (E : Finset (Atom IA IU)) : Finset IU := by
  classical
  exact Finset.univ.filter (fun i => Sum.inr i ∈ E)

@[simp] theorem actionAtoms_empty
    {IA : Type uI} {IU : Type uJ} [Fintype IA] :
    actionAtoms (IA := IA) (IU := IU) ∅ = ∅ := by
  classical
  simp [actionAtoms]

@[simp] theorem updateAtoms_empty
    {IA : Type uI} {IU : Type uJ} [Fintype IU] :
    updateAtoms (IA := IA) (IU := IU) ∅ = ∅ := by
  classical
  simp [updateAtoms]

/-- Actual block model over the original canonical typed α → P → U machine. -/
noncomputable def atomicBlockModel
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ}
    [Fintype IA] [Fintype IU] [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (E : Finset (Atom IA IU)) :
    PermanssonLean.StrategicWorldModel S X A :=
  let α := patchedAction M bank (actionAtoms E)
  let U := patchedUpdate M bank (updateAtoms E)
  { generator := {
      action := α.kernel
      update := U.kernel
      action_isMarkov := α.isMarkov
      update_isMarkov := U.isMarkov
    }
    world := M.world
    world_isMarkov := M.world_isMarkov }

/-- A component block has *one* genuine model determined by its atom expansion. -/
noncomputable def blockModel
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (Γ : PartitionGrammar IA IU C)
    (D : Finset C) :
    PermanssonLean.StrategicWorldModel S X A :=
  atomicBlockModel M bank (Γ.expand D)

@[simp] theorem atomicBlockModel_world
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ}
    [Fintype IA] [Fintype IU] [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU) (E : Finset (Atom IA IU)) :
    (atomicBlockModel M bank E).world = M.world := rfl

@[simp] theorem blockModel_world
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (Γ : PartitionGrammar IA IU C) (D : Finset C) :
    (blockModel M bank Γ D).world = M.world := rfl

theorem blockModel_eq_of_expand_eq
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ} {C₁ : Type uC} {C₂ : Type*}
    [Fintype IA] [Fintype IU] [Fintype C₁] [Fintype C₂]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (Γ₁ : PartitionGrammar IA IU C₁)
    (Γ₂ : PartitionGrammar IA IU C₂)
    (D₁ : Finset C₁) (D₂ : Finset C₂)
    (h : Γ₁.expand D₁ = Γ₂.expand D₂) :
    blockModel M bank Γ₁ D₁ = blockModel M bank Γ₂ D₂ := by
  simp only [blockModel, h]

theorem atomicBlockModel_empty_generator_action
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ}
    [Fintype IA] [Fintype IU] [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU) :
    (atomicBlockModel M bank ∅).generator.action = M.generator.action := by
  simp [atomicBlockModel]

theorem atomicBlockModel_empty_generator_update
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ}
    [Fintype IA] [Fintype IU] [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU) :
    (atomicBlockModel M bank ∅).generator.update = M.generator.update := by
  simp [atomicBlockModel]

end GrammarRobust
end PermanssonResearch
