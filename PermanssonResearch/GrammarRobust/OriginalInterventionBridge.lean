import PermanssonResearch.GrammarRobust.BlockModels
import PermanssonLean.Regime.UniformPermansson

/-!
# Lane B — bridge back to original v0.1.8 typed intervention semantics

Every selected semantic block produces one actual whole strategic generator.
It is injected into the original `.jointStrategic` target with a frozen
component/allowed-block admission predicate.  No new meaning of PR is defined.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust

universe uS uX uA uI uJ uC

/-- Original typed intervention family whose components are complete selected
blocks.  Admission requires both the frozen block feasibility and the exact
constructed generator for that block. -/
noncomputable def blockFamily
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (Γ : PartitionGrammar IA IU C) :
    PermanssonLean.InterventionFamily M (Finset C) where
  targetOf := fun _ => .jointStrategic
  admissible := fun D r =>
    Γ.allowed D ∧ r = (blockModel M bank Γ D).generator

/-- Every admitted block is installed as a genuine typed strategic
intervention, with a replacement computed from physical row patches. -/
noncomputable def admittedBlockIntervention
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (Γ : PartitionGrammar IA IU C)
    (D : AllowedBlock Γ) :
    PermanssonLean.AdmissibleStrategicIntervention (blockFamily M bank Γ) := by
  let J : PermanssonLean.TypedIntervention (blockFamily M bank Γ) :=
    { component := D.components
      replacement := (blockModel M bank Γ D.components).generator }
  refine ⟨J, ?_, ?_⟩
  · exact ⟨D.accepted, rfl⟩
  · trivial

/-- Literal model equality: old single-target `.jointStrategic` application
and new multi-atom construction have exactly the same canonical α, P and U. -/
theorem admittedBlockIntervention_apply
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (Γ : PartitionGrammar IA IU C)
    (D : AllowedBlock Γ) :
    (admittedBlockIntervention M bank Γ D).intervention.apply =
      blockModel M bank Γ D.components := by
  rfl

end GrammarRobust
end PermanssonResearch
