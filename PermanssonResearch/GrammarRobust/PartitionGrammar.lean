import PermanssonResearch.GrammarRobust.AtomicApply
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Lane B — frozen semantic component partitions

The physical atoms remain unchanged while their grouping into named semantic
components varies.  All admitted component blocks are frozen before evaluation.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust

universe uI uJ uC

/-- Finite partitions of a shared bank of physical atoms.
The admissible-block predicate is not assumed downward-closed. -/
structure PartitionGrammar
    (IA : Type uI) (IU : Type uJ) (Component : Type uC)
    [Fintype IA] [Fintype IU] [Fintype Component] where
  atomsOf : Component → Finset (Atom IA IU)
  nonempty : ∀ c, (atomsOf c).Nonempty
  disjoint : ∀ c d, c ≠ d → Disjoint (atomsOf c) (atomsOf d)
  cover : ∀ a : Atom IA IU, ∃ c, a ∈ atomsOf c
  allowed : Finset Component → Prop
  allowed_empty : allowed ∅

/-- The actual physical atoms selected by a semantic block. -/
noncomputable def PartitionGrammar.expand
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    (Γ : PartitionGrammar IA IU C)
    (D : Finset C) : Finset (Atom IA IU) := by
  classical
  exact D.biUnion Γ.atomsOf

@[simp] theorem PartitionGrammar.expand_empty
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    (Γ : PartitionGrammar IA IU C) :
    Γ.expand ∅ = ∅ := by
  classical
  simp [PartitionGrammar.expand]

/-- An admissible semantic block is a *proved* frozen selection,
not an arbitrary collection of component names. -/
structure AllowedBlock
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    (Γ : PartitionGrammar IA IU C) where
  components : Finset C
  accepted : Γ.allowed components

noncomputable def AllowedBlock.empty
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    (Γ : PartitionGrammar IA IU C) : AllowedBlock Γ :=
  ⟨∅, Γ.allowed_empty⟩

end GrammarRobust
end PermanssonResearch
