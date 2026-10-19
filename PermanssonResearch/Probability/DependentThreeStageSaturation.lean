import PermanssonResearch.ReverseSolver.ChronologicalMonitorMeasure
import PermanssonResearch.Probability.DependentHistoryCommonMass
import Mathlib.Tactic

/-!
# NEXT-03 / Q-03: dependent three-stage finite history, exact saturation

The state is the entire chronological Boolean three-observation history.
After the first failure, the process stays failed: second and third rows
are therefore HISTORY-CONDITIONAL, not unconditionally independent Bernoulli
errors. On surviving histories the conditional error rates are 1/10, 1/5,
1/4, with retained mass 27/50 and discrepancy 23/50 from all-success.

This is a finite constructed conditional product law. The independent Python
test checks the event-supremum metric over all 256 subsets of eight paths;
the present Lean source checks its complete normalized atoms and half-L1
value, not a general identification with arbitrary infinite path laws.
-/

namespace PermanssonResearch.Probability.DependentThreeStage

open PermanssonResearch.ReverseSolver.FiniteMonitor

abbrev History := Bool × (Bool × Bool)

/-- Stage zero success is 9/10. -/
def initialStep (success : Bool) : ℚ :=
  if success then 9 / 10 else 1 / 10

/-- Actual chronological row: once failure occurs, future success is
impossible. This makes stage outcomes dependent under the full law. -/
def nextRow (prior next : Bool) (η : ℚ) : ℚ :=
  if prior then (if next then 1 - η else η)
  else (if next then 0 else 1)

/-- Complete probability mass of an exact three-observation history. -/
def dependentAtom (w : History) : ℚ :=
  initialStep w.1 * nextRow w.1 w.2.1 (1 / 5) *
    nextRow w.2.1 w.2.2 (1 / 4)

/-- The reference path law remains successful on every stage. -/
def perfectAtom (w : History) : ℚ :=
  if w = (true, (true, true)) then 1 else 0

noncomputable def dependentLaw : FiniteProbabilityLaw History where
  support := Finset.univ
  atom w := (dependentAtom w : ℝ)
  nonnegative w := by
    rcases w with ⟨a, b, c⟩
    cases a <;> cases b <;> cases c <;>
      norm_num [dependentAtom, initialStep, nextRow]
  supported w hw := False.elim (hw (Finset.mem_univ w))
  normalized := by
    norm_num [dependentAtom, initialStep, nextRow,
      Fintype.sum_prod_type, Fintype.sum_bool]

noncomputable def perfectLaw : FiniteProbabilityLaw History where
  support := Finset.univ
  atom w := (perfectAtom w : ℝ)
  nonnegative w := by
    rcases w with ⟨a, b, c⟩
    cases a <;> cases b <;> cases c <;>
      norm_num [perfectAtom]
  supported w hw := False.elim (hw (Finset.mem_univ w))
  normalized := by
    norm_num [perfectAtom, Fintype.sum_prod_type, Fintype.sum_bool]

/-- Actual survivor-history mass, the product of conditional retained rows. -/
theorem true_history_mass :
    dependentLaw.atom (true, (true, true)) = 27 / 50 := by
  norm_num [dependentLaw, dependentAtom, initialStep, nextRow]

/-- A bona fide normalized finite-probability example with half L1 of 23/50.
Event-TV equality in this finite context is independently exhausted over every
event in the Python fixture; no general infinite-law identity is assumed. -/
noncomputable def finiteHalfL1 : ℝ :=
  (∑ w : History, |dependentLaw.atom w - perfectLaw.atom w|) / 2

theorem dependent_three_stage_halfL1_exact :
    finiteHalfL1 = 23 / 50 := by
  norm_num [finiteHalfL1, dependentLaw, perfectLaw, dependentAtom,
    perfectAtom, initialStep, nextRow, Fintype.sum_prod_type,
    Fintype.sum_bool]

/-- The retained row mass is exactly (9/10)(4/5)(3/4), not the
naive independent *error probability* sum 1/10+1/5+1/4. -/
theorem actual_retained_product :
    (1 - (1 / 10 : ℚ)) * (1 - 1 / 5) * (1 - 1 / 4) = 27 / 50 := by
  norm_num

end PermanssonResearch.Probability.DependentThreeStage
