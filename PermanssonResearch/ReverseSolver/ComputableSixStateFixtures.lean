import PermanssonResearch.ReverseSolver.ConstitutiveCertificateCheck
import PermanssonResearch.MultipleLimit.ExactSixStateC8SupportWitness
import PermanssonResearch.ReverseSolver.ExactSixStateC9MenuWitness
import Mathlib.Tactic

/-!
# C10 — executable rational six-state matrices and original typed witnesses

The C8 half/tiny and C9 one-row definitions were written inside
noncomputable sections. Reify their exact entries here as total
computable pure rational functions, then prove extensional correspondence
rather than declaring the new data identical by fiat. The B-only variant
was previously only an independently tested Python fixture and is now
constructed as a genuine typed alpha-only intervention.
-/
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open PermanssonResearch.MultipleLimit.ExactSixState
open PermanssonResearch.MultipleLimit.ExactSixStateCanonical
open PermanssonResearch.MultipleLimit.ExactSixStateC8SupportWitness
open PermanssonResearch.ReverseSolver.ExactSixStateC9MenuWitness
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonLean

/-- Computable parameterization of the C8 response rows. -/
def softEntryExecutable (ε : ℚ) (i j : Fin 6) : ℚ :=
  if i = 1 then (if j = 1 then 1 else 0)
  else if i = 2 then
    (if j = 1 then ε else if j = 4 then 1 - ε else 0)
  else transition i j

def halfEntryExecutable (i j : Fin 6) : ℚ :=
  softEntryExecutable (1/2) i j

def tinyEntryExecutable (i j : Fin 6) : ℚ :=
  softEntryExecutable (1/1000) i j

/-- C6 full two-row disruption in executable exact rational form. -/
def fullEntryExecutable (i j : Fin 6) : ℚ :=
  if i = 1 ∨ i = 2 then
    (if j = 1 then 1 else 0)
  else transition i j

/-- C9 genuine one-row partial response, reified as pure data. -/
def uOnlyEntryExecutable (i j : Fin 6) : ℚ :=
  if i = 1 then (if j = 1 then 1 else 0)
  else transition i j

/-- The extra B-only exact target, absent from earlier typed Lean files. -/
def bOnlyEntryExecutable (i j : Fin 6) : ℚ :=
  if i = 1 ∨ i = 2 then
    (if j = 4 then 1 else 0)
  else transition i j

/-- C9 one-row partial response, now with pure executable entries. -/
def oneRowEntryExecutable (i j : Fin 6) : ℚ :=
  if i = 1 then (if j = 1 then 1 else 0)
  else transition i j

private theorem half_nonneg (i j : Fin 6) :
    0 ≤ halfEntryExecutable i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [halfEntryExecutable, softEntryExecutable, transition]

private theorem half_rows (i : Fin 6) :
    (∑ j : Fin 6, halfEntryExecutable i j) = 1 := by
  fin_cases i <;>
    norm_num [halfEntryExecutable, softEntryExecutable, transition,
      Fin.sum_univ_succ]

private theorem tiny_nonneg (i j : Fin 6) :
    0 ≤ tinyEntryExecutable i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [tinyEntryExecutable, softEntryExecutable, transition]

private theorem tiny_rows (i : Fin 6) :
    (∑ j : Fin 6, tinyEntryExecutable i j) = 1 := by
  fin_cases i <;>
    norm_num [tinyEntryExecutable, softEntryExecutable, transition,
      Fin.sum_univ_succ]

private theorem full_nonneg (i j : Fin 6) :
    0 ≤ fullEntryExecutable i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [fullEntryExecutable, transition]

private theorem full_rows (i : Fin 6) :
    (∑ j : Fin 6, fullEntryExecutable i j) = 1 := by
  fin_cases i <;>
    norm_num [fullEntryExecutable, transition, Fin.sum_univ_succ]

private theorem uOnly_nonneg (i j : Fin 6) :
    0 ≤ uOnlyEntryExecutable i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [uOnlyEntryExecutable, transition]

private theorem uOnly_rows (i : Fin 6) :
    (∑ j : Fin 6, uOnlyEntryExecutable i j) = 1 := by
  fin_cases i <;>
    norm_num [uOnlyEntryExecutable, transition, Fin.sum_univ_succ]

private theorem bOnly_nonneg (i j : Fin 6) :
    0 ≤ bOnlyEntryExecutable i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [bOnlyEntryExecutable, transition]

private theorem bOnly_rows (i : Fin 6) :
    (∑ j : Fin 6, bOnlyEntryExecutable i j) = 1 := by
  fin_cases i <;>
    norm_num [bOnlyEntryExecutable, transition, Fin.sum_univ_succ]

private theorem oneRow_nonneg (i j : Fin 6) :
    0 ≤ oneRowEntryExecutable i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [oneRowEntryExecutable, transition]

private theorem oneRow_rows (i : Fin 6) :
    (∑ j : Fin 6, oneRowEntryExecutable i j) = 1 := by
  fin_cases i <;>
    norm_num [oneRowEntryExecutable, transition, Fin.sum_univ_succ]

def fullMatrixExecutable : RationalMarkovMatrix 6 where
  entry := fullEntryExecutable
  entry_nonneg := full_nonneg
  row_sum_one := full_rows

def uOnlyMatrixExecutable : RationalMarkovMatrix 6 where
  entry := uOnlyEntryExecutable
  entry_nonneg := uOnly_nonneg
  row_sum_one := uOnly_rows

def halfMatrixExecutable : RationalMarkovMatrix 6 where
  entry := halfEntryExecutable
  entry_nonneg := half_nonneg
  row_sum_one := half_rows

def tinyMatrixExecutable : RationalMarkovMatrix 6 where
  entry := tinyEntryExecutable
  entry_nonneg := tiny_nonneg
  row_sum_one := tiny_rows

def bOnlyMatrixExecutable : RationalMarkovMatrix 6 where
  entry := bOnlyEntryExecutable
  entry_nonneg := bOnly_nonneg
  row_sum_one := bOnly_rows

def oneRowMatrixExecutable : RationalMarkovMatrix 6 where
  entry := oneRowEntryExecutable
  entry_nonneg := oneRow_nonneg
  row_sum_one := oneRow_rows

/-- Exact entrywise identification with the old original C8 matrices;
this does not treat mere positive-support equality as numeric equality. -/
theorem halfEntryExecutable_eq_original (i j : Fin 6) :
    halfMatrixExecutable.entry i j = halfMatrix.entry i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [halfMatrixExecutable, halfEntryExecutable,
      softEntryExecutable, halfMatrix, halfEntry, softEntry, transition]

theorem tinyEntryExecutable_eq_original (i j : Fin 6) :
    tinyMatrixExecutable.entry i j = tinyMatrix.entry i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [tinyMatrixExecutable, tinyEntryExecutable,
      softEntryExecutable, tinyMatrix, tinyEntry, softEntry, transition]

theorem oneRowEntryExecutable_eq_original (i j : Fin 6) :
    oneRowMatrixExecutable.entry i j = oneRowMatrix.entry i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [oneRowMatrixExecutable, oneRowEntryExecutable,
      oneRowMatrix, oneRowEntry, transition]

/-- Reified C6 full disruption is entrywise identical to its frozen source. -/
theorem fullEntryExecutable_eq_original (i j : Fin 6) :
    fullMatrixExecutable.entry i j =
      PermanssonResearch.MultipleLimit.ExactSixStateTargetDisruption.disruptedMatrix.entry i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [fullMatrixExecutable, fullEntryExecutable,
      PermanssonResearch.MultipleLimit.ExactSixStateTargetDisruption.disruptedMatrix,
      PermanssonResearch.MultipleLimit.ExactSixStateTargetDisruption.disruptedEntry,
      transition]

/-- Newly constructed typed B-only member, not a test-only matrix. -/
noncomputable def bOnlyJ :
    AdmissibleStrategicIntervention (researchActionFamily sixStateMatrix) :=
  rationalStrategicIntervention sixStateMatrix bOnlyMatrixExecutable

theorem bOnly_world_fixed :
    bOnlyJ.intervention.apply.world = (realizedModel sixStateMatrix).world :=
  rationalStrategicIntervention_world_fixed _ _

theorem bOnly_update_fixed :
    bOnlyJ.intervention.apply.generator.update =
      (realizedModel sixStateMatrix).generator.update :=
  rationalStrategicIntervention_update_fixed _ _

end C10
end ReverseSolver
end PermanssonResearch