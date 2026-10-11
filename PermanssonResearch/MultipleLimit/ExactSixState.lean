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
  decide

theorem transition_row_sum : ∀ i : Fin 6, ∑ j : Fin 6, transition i j = 1 := by
  decide

def rationalTransition : FiniteCommunication.RationalTransition (Fin 6) where
  entry := transition
  nonneg := transition_nonneg
  row_sum := transition_row_sum

def classA : Set (Fin 6) := {i | i = 2 ∨ i = 3}
def classB : Set (Fin 6) := {i | i = 4 ∨ i = 5}

theorem classA_closed :
    rationalTransition.ClosedSubset classA := by
  decide

theorem classB_closed :
    rationalTransition.ClosedSubset classB := by
  decide

theorem classA_disjoint_classB : Disjoint classA classB := by
  intro x hx
  rcases hx with ⟨hA, hB⟩
  simp [classA, classB] at hA hB
  omega

theorem classA_period_two_rows :
    transition 2 3 = 1 ∧ transition 3 2 = 1 ∧
    transition 2 2 = 0 ∧ transition 3 3 = 0 := by
  decide

theorem classB_self_loop :
    transition 4 4 = 1/2 ∧ transition 5 5 = 3/4 := by
  decide

def piA (i : Fin 6) : ℚ :=
  if i = 2 ∨ i = 3 then 1/2 else 0

def piB (i : Fin 6) : ℚ :=
  if i = 4 then 1/3 else if i = 5 then 2/3 else 0

theorem piA_normalized : (∑ i : Fin 6, piA i) = 1 := by
  decide

theorem piB_normalized : (∑ i : Fin 6, piB i) = 1 := by
  decide

theorem piA_nonneg : ∀ i : Fin 6, 0 ≤ piA i := by
  decide

theorem piB_nonneg : ∀ i : Fin 6, 0 ≤ piB i := by
  decide

theorem piA_stationary :
    ∀ j : Fin 6, ∑ i : Fin 6, piA i * transition i j = piA j := by
  decide

theorem piB_stationary :
    ∀ j : Fin 6, ∑ i : Fin 6, piB i * transition i j = piB j := by
  decide

/-- Candidate eventual A/B weights; harmonicity is the proved finite
linear identity, *not* yet a canonical probability-of-ever-hitting theorem. -/
def weightA (i : Fin 6) : ℚ :=
  if i = 0 ∨ i = 1 then 1/3 else if i = 2 ∨ i = 3 then 1 else 0

def weightB (i : Fin 6) : ℚ :=
  1 - weightA i

theorem weights_normalized : ∀ i : Fin 6, weightA i + weightB i = 1 := by
  decide

theorem weights_nonneg :
    (∀ i : Fin 6, 0 ≤ weightA i) ∧
    (∀ i : Fin 6, 0 ≤ weightB i) := by
  decide

theorem weightA_harmonic :
    ∀ i : Fin 6,
      (∑ j : Fin 6, transition i j * weightA j) = weightA i := by
  decide

theorem weightB_harmonic :
    ∀ i : Fin 6,
      (∑ j : Fin 6, transition i j * weightB j) = weightB i := by
  decide

theorem transient_weights :
    weightA 0 = 1/3 ∧ weightB 0 = 2/3 ∧
    weightA 1 = 1/3 ∧ weightB 1 = 2/3 := by
  decide

theorem observed_collapse :
    (2 : Fin 6) ≠ 4 ∧
    (if (2 : Fin 6) = 2 ∨ (2 : Fin 6) = 3 then true else true) =
    (if (4 : Fin 6) = 2 ∨ (4 : Fin 6) = 3 then true else true) := by
  decide

end ExactSixState
end MultipleLimit
end PermanssonResearch
