import PermanssonResearch.GrammarRobust.AtomicBank
import Mathlib.Data.Finset.Sort

/-!
# Lane B — actual measurable simultaneous atomic kernel replacements

Each selected row is replaced by the frozen physical patch kernel, with
unselected rows inherited from the original primitive.  The sorting of
physical atoms is only an implementation detail.  Disjointness is the
scientific precondition for order independence.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust

universe uS uX uA uI uJ

/-- Install a row-local patch over a previously valid Markov kernel.
The resulting kernel is measurable and normalized by construction. -/
noncomputable def applyRowPatch
    {Input Output : Type*}
    [MeasurableSpace Input] [MeasurableSpace Output]
    (p : RowPatch Input Output)
    (current : PermanssonLean.MarkovKernelReplacement Input Output) :
    PermanssonLean.MarkovKernelReplacement Input Output := by
  classical
  letI : IsMarkovKernel p.replacement := p.replacement_isMarkov
  letI : IsMarkovKernel current.kernel := current.isMarkov
  exact ⟨Kernel.piecewise p.measurable_region p.replacement current.kernel, inferInstance⟩

theorem applyRowPatch_selected
    {Input Output : Type*}
    [MeasurableSpace Input] [MeasurableSpace Output]
    (p : RowPatch Input Output)
    (current : PermanssonLean.MarkovKernelReplacement Input Output)
    (x : Input) (hx : x ∈ p.region) :
    (applyRowPatch p current).kernel x = p.replacement x := by
  classical
  simp [applyRowPatch, Kernel.piecewise_apply, hx]

theorem applyRowPatch_unselected
    {Input Output : Type*}
    [MeasurableSpace Input] [MeasurableSpace Output]
    (p : RowPatch Input Output)
    (current : PermanssonLean.MarkovKernelReplacement Input Output)
    (x : Input) (hx : x ∉ p.region) :
    (applyRowPatch p current).kernel x = current.kernel x := by
  classical
  simp [applyRowPatch, Kernel.piecewise_apply, hx]

/-- Install the declared action atoms in a deterministic enumeration.
Every intermediate kernel is Markov by type. -/
noncomputable def patchedAction
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ}
    [LinearOrder IA]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (selected : Finset IA) :
    PermanssonLean.MarkovKernelReplacement (PermanssonLean.JointState S X) A :=
  (selected.sort (· ≤ ·)).foldl
    (fun current i => applyRowPatch (bank.action i) current)
    ⟨M.generator.action, M.generator.action_isMarkov⟩

/-- Install the declared strategic-update atoms; world P is never touched. -/
noncomputable def patchedUpdate
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ}
    [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (selected : Finset IU) :
    PermanssonLean.MarkovKernelReplacement (PermanssonLean.UpdateInput S X A) S :=
  (selected.sort (· ≤ ·)).foldl
    (fun current i => applyRowPatch (bank.update i) current)
    ⟨M.generator.update, M.generator.update_isMarkov⟩

@[simp] theorem patchedAction_empty
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ} [LinearOrder IA]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU) :
    (patchedAction M bank ∅).kernel = M.generator.action := by
  simp [patchedAction]

@[simp] theorem patchedUpdate_empty
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ} [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU) :
    (patchedUpdate M bank ∅).kernel = M.generator.update := by
  simp [patchedUpdate]

end GrammarRobust
end PermanssonResearch
