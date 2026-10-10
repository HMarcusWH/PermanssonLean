import PermanssonLean.Intervention.Apply
import Mathlib.Probability.Kernel.Basic
import Mathlib.Data.Finset.Sort

/-!
# Lane B — finite bank of physical, measurable, row-local strategic patches

Atomic patches are not semantic components.  The former target rows of a
single strategic kernel; the latter are partitions of these atoms.
The bank is frozen *before* any block is selected.  Physical patch effects
are supplied as actual Markov kernels, rather than an assumed post-block model.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace GrammarRobust

universe uS uX uA uI uJ

/-- A replacement of a measurable subset of input rows of a Markov kernel. -/
structure RowPatch (Input Output : Type*)
    [MeasurableSpace Input] [MeasurableSpace Output] where
  region : Set Input
  measurable_region : MeasurableSet region
  replacement : Kernel Input Output
  replacement_isMarkov : IsMarkovKernel replacement

/-- Physical atomic bank.  Distinct patches of a given primitive have
pairwise disjoint measurable input-row regions.  Action and update patches
live on different input spaces and therefore never conflict. -/
structure AtomicBank
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (AAtom : Type uI) (UAtom : Type uJ) where
  action : AAtom → RowPatch (PermanssonLean.JointState S X) A
  update : UAtom → RowPatch (PermanssonLean.UpdateInput S X A) S
  action_disjoint : ∀ i j, i ≠ j →
    Disjoint (action i).region (action j).region
  update_disjoint : ∀ i j, i ≠ j →
    Disjoint (update i).region (update j).region

/-- The physical atom type, with a target fixed at the type level. -/
abbrev Atom (AAtom : Type uI) (UAtom : Type uJ) :=
  Sum AAtom UAtom

end GrammarRobust
end PermanssonResearch
