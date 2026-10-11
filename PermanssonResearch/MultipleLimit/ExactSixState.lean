import PermanssonResearch.MultipleLimit.FiniteCommunication
import Mathlib.Tactic

/-!
# Lane C2 — exact six-state recurrent-class witness

A six-state rational transition system with two transient states, a
non-singleton period-two closed class and a non-singleton aperiodic closed
class. All claims below are exact finite arithmetic, *not* statements about
an infinite canonical path law or a general Markov-chain ergodic theorem.

States:
0=t, 1=u, 2=a0, 3=a1, 4=b0, 5=b1.
t→u with mass 1.
u→u,a0,b0 with weights 1/2, 1/6, 1/3.
a0↔a1 deterministically.
b0→b0,b1 with weights 1/2,1/2.
b1→b0,b1 with weights 1/4,3/4.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixState

def transition (i j : Fin 6) : ℚ :=
  if i = 0 then
    if j = 1 then 1 else 0
  else if i = 1 then
    if j = 1 then 1/2 else if j = 2 then 1/6 else if j = 4 then 1/3 else 0
  else if i = 2 then
    if j = 3 then 1 else 0
  else if i = 3 then
    if j = 2 then 1 else 0
  else if i = 4 then
    if j = 4 then 1/2 else if j = 5 then 1/2 else 0
  else
    if j = 4 then 1/4 else if j = 5 then 3/4 else 0

theorem transition_nonneg : ∀ i j : Fin 6, 0 ≤ transition i j := by
  intro i j
  unfold transition
  split_ifs <;> norm_num

theorem transition_row_sum : ∀ i : Fin 6, ∑ j : Fin 6, transition i j = 1 := by
  intro i
  fin_cases i <;> norm_num [transition, Fin.sum_univ_succ]

def rationalTransition : FiniteCommunication.RationalTransition (Fin 6) where
  entry := transition
  nonneg := transition_nonneg
  row_sum := transition_row_sum

def classA : Set (Fin 6) := {i | i = 2 ∨ i = 3}
def classB : Set (Fin 6) := {i | i = 4 ∨ i = 5}

theorem classA_closed :
    rationalTransition.ClosedSubset classA := by
  intro i hi j hij
  fin_cases i <;> fin_cases j <;>
    norm_num [classA, rationalTransition,
      FiniteCommunication.RationalTransition.PositiveEdge, transition] at *

theorem classB_closed :
    rationalTransition.ClosedSubset classB := by
  intro i hi j hij
  fin_cases i <;> fin_cases j <;>
    norm_num [classB, rationalTransition,
      FiniteCommunication.RationalTransition.PositiveEdge, transition] at *

theorem classA_disjoint_classB : Disjoint classA classB := by
  apply Set.disjoint_left.mpr
  intro x hxA hxB
  fin_cases x <;> simp [classA, classB] at *

theorem classA_period_two_rows :
    transition 2 3 = 1 ∧ transition 3 2 = 1 ∧
    transition 2 2 = 0 ∧ transition 3 3 = 0 := by
  decide

theorem classB_self_loop :
    transition 4 4 = 1/2 ∧ transition 5 5 = 3/4 := by
  norm_num [transition]

def piA (i : Fin 6) : ℚ :=
  if i = 2 ∨ i = 3 then 1/2 else 0

def piB (i : Fin 6) : ℚ :=
  if i = 4 then 1/3 else if i = 5 then 2/3 else 0

theorem piA_normalized : (∑ i : Fin 6, piA i) = 1 := by
  norm_num [piA, Fin.sum_univ_succ]

theorem piB_normalized : (∑ i : Fin 6, piB i) = 1 := by
  norm_num [piB, Fin.sum_univ_succ]

theorem piA_nonneg : ∀ i : Fin 6, 0 ≤ piA i := by
  intro i
  fin_cases i <;> norm_num [piA]

theorem piB_nonneg : ∀ i : Fin 6, 0 ≤ piB i := by
  intro i
  fin_cases i <;> norm_num [piB]

theorem piA_stationary :
    ∀ j : Fin 6, ∑ i : Fin 6, piA i * transition i j = piA j := by
  intro j
  fin_cases j <;> norm_num [piA, transition, Fin.sum_univ_succ]

theorem piB_stationary :
    ∀ j : Fin 6, ∑ i : Fin 6, piB i * transition i j = piB j := by
  intro j
  fin_cases j <;> norm_num [piB, transition, Fin.sum_univ_succ]

/-- Candidate eventual A/B weights; harmonicity is the proved finite
linear identity, *not* yet a canonical probability-of-ever-hitting theorem. -/
def weightA (i : Fin 6) : ℚ :=
  if i = 0 ∨ i = 1 then 1/3 else if i = 2 ∨ i = 3 then 1 else 0

def weightB (i : Fin 6) : ℚ :=
  1 - weightA i

theorem weights_normalized : ∀ i : Fin 6, weightA i + weightB i = 1 := by
  intro i
  fin_cases i <;> norm_num [weightA, weightB]

theorem weights_nonneg :
    (∀ i : Fin 6, 0 ≤ weightA i) ∧
    (∀ i : Fin 6, 0 ≤ weightB i) := by
  constructor <;> intro i <;> fin_cases i <;>
    norm_num [weightA, weightB]

theorem weightA_harmonic :
    ∀ i : Fin 6,
      (∑ j : Fin 6, transition i j * weightA j) = weightA i := by
  intro i
  fin_cases i <;> norm_num [weightA, transition, Fin.sum_univ_succ]

theorem weightB_harmonic :
    ∀ i : Fin 6,
      (∑ j : Fin 6, transition i j * weightB j) = weightB i := by
  intro i
  fin_cases i <;> norm_num [weightB, weightA, transition, Fin.sum_univ_succ]

theorem transient_weights :
    weightA 0 = 1/3 ∧ weightB 0 = 2/3 ∧
    weightA 1 = 1/3 ∧ weightB 1 = 2/3 := by
  norm_num [weightA, weightB]

def observedRecurrent (i : Fin 6) : Bool :=
  if i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 then true else false

theorem observed_collapse_and_nonconstant :
    observedRecurrent 2 = observedRecurrent 4 ∧
    observedRecurrent 0 ≠ observedRecurrent 2 := by
  decide

end ExactSixState
end MultipleLimit
end PermanssonResearch
