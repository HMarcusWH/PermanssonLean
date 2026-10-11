import PermanssonResearch.MultipleLimit.ExactSixState
import Mathlib.Tactic

/-!
# Lane C2 — exact rational recurrent-class lumpability

This checks every six-state transition row against the four-state quotient
t,u,A,B. It does not claim a pushed-forward canonical infinite path measure
until a generic Markov-kernel and path-law bridge has been proved.

In the quotient A and B are absorbing, despite the underlying A class being
strictly period two and B being aperiodic. The distinction is the point.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateQuotient

open ExactSixState

def classQuotient (i : Fin 6) : Fin 4 :=
  if i = 0 then 0
  else if i = 1 then 1
  else if i = 2 ∨ i = 3 then 2
  else 3

def quotientTransition (i j : Fin 4) : ℚ :=
  if i = 0 then
    if j = 1 then 1 else 0
  else if i = 1 then
    if j = 1 then 1/2 else if j = 2 then 1/6 else if j = 3 then 1/3 else 0
  else if i = 2 then
    if j = 2 then 1 else 0
  else
    if j = 3 then 1 else 0

theorem quotient_rows_normalized :
    ∀ i : Fin 4, ∑ j : Fin 4, quotientTransition i j = 1 := by
  decide

theorem quotient_rows_nonneg :
    ∀ i j : Fin 4, 0 ≤ quotientTransition i j := by
  decide

/-- Genuine exact finite-state row lumpability; each quotient transition
is the total original transition mass into its preimage class. -/
theorem class_quotient_exact :
    ∀ i : Fin 6, ∀ j : Fin 4,
      (∑ z : Fin 6,
        if classQuotient z = j then transition i z else 0) =
      quotientTransition (classQuotient i) j := by
  decide

/-- The two class-supported stationary candidates push forward to
different quotient Dirac masses. -/
theorem piA_pushes_to_A :
    ∀ j : Fin 4,
      (∑ i : Fin 6, if classQuotient i = j then piA i else 0) =
      if j = 2 then 1 else 0 := by
  decide

theorem piB_pushes_to_B :
    ∀ j : Fin 4,
      (∑ i : Fin 6, if classQuotient i = j then piB i else 0) =
      if j = 3 then 1 else 0 := by
  decide

theorem class_quotient_noninjective :
    classQuotient 2 = classQuotient 3 ∧
    (2 : Fin 6) ≠ 3 := by
  decide

end ExactSixStateQuotient
end MultipleLimit
end PermanssonResearch
