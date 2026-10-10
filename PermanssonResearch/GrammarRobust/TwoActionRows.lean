import PermanssonResearch.GrammarRobust.AtomicSelection
import PermanssonResearch.GrammarRobust.BooleanModel
import Mathlib.Tactic

/-!
# Lane B — two genuinely distinct action-row interventions

This model has two physical action atoms with disjoint nonempty input-row
regions. One selects rows where the strategic bit is false and one selects
rows where it is true. The world primitive P and all update rows are fixed.
The example rules out treating an action primitive as a single indivisible
on/off switch and certifies noninterference on an unselected row.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust
namespace TwoActionRows

open PermanssonLean BooleanModel

def mask (i : Fin 2) : Set Y :=
  if i = 0 then {y | y.1 = false} else {y | y.1 = true}

private theorem mask_measurable (i : Fin 2) :
    MeasurableSet (mask i) := MeasurableSet.of_discrete

noncomputable def bank : AtomicBank baseline (Fin 2) (Fin 0) where
  action := fun i => {
    region := mask i
    measurable_region := mask_measurable i
    replacement := actionFalse
    replacement_isMarkov := by unfold actionFalse; infer_instance }
  update := fun i => Fin.elim0 i
  action_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · apply Set.disjoint_left.mpr
      intro y hy hz
      simp [mask] at hy hz
      exact Bool.false_ne_true (hy.symm.trans hz)
    · apply Set.disjoint_left.mpr
      intro y hy hz
      simp [mask] at hy hz
      exact Bool.false_ne_true (hz.symm.trans hy)
    · exact (hij rfl).elim
  update_disjoint := by
    intro i
    exact Fin.elim0 i

theorem row_false_selected :
    (patchedAction baseline bank ({0} : Finset (Fin 2))).kernel
      (false, false) = actionFalse (false, false) := by
  have hy : (false, false) ∈ (bank.action (0 : Fin 2)).region := by
    simp [bank, mask]
  have h := applyRowPatch_selected (bank.action (0 : Fin 2))
    (⟨baseline.generator.action, baseline.generator.action_isMarkov⟩ :
      MarkovKernelReplacement Y Bool) (false,false) hy
  simpa [patchedAction] using h

theorem row_true_unchanged :
    (patchedAction baseline bank ({0} : Finset (Fin 2))).kernel
      (true, true) = baseline.generator.action (true, true) := by
  apply patchedAction_unaffected
  intro i hi
  have hi0 : i = (0 : Fin 2) := by simpa using hi
  subst i
  simp [bank, mask]

end TwoActionRows
end GrammarRobust
end PermanssonResearch
