import PermanssonResearch.Quotient.GeometricPrefix
import Mathlib.Tactic

/-!
# Q-01: a deterministic fine transition need not descend to its projection

Two genuine fine states share their coarse visible state while their next
coarse states differ. Hence no uniform autonomous deterministic coarse
transition exists. This is a sufficient finite non-lumpability witness,
NOT a claim that every particular projected path law is non-Markov or that
the geometric-prefix theorem requires a projected Markov hypothesis.
-/

namespace PermanssonResearch.Quotient.Q01NonLumpable
set_option autoImplicit false

def observed (x : Fin 3) : Bool := x = 1

def fineStep (x : Fin 3) : Fin 3 :=
  if x = 0 then 1 else 0

theorem equal_current_observation :
    observed (0 : Fin 3) = observed (2 : Fin 3) := by
  decide

theorem incompatible_next_observations :
    observed (fineStep (0 : Fin 3)) ≠ observed (fineStep (2 : Fin 3)) := by
  decide

/-- There is no state-only coarse evolution map that represents this
fine deterministic transition for every allowed fine starting state. -/
theorem no_autonomous_coarse_transition :
    ¬ ∃ g : Bool → Bool, ∀ x : Fin 3,
        observed (fineStep x) = g (observed x) := by
  rintro ⟨g, hg⟩
  have h0 := hg 0
  have h2 := hg 2
  apply incompatible_next_observations
  calc
    observed (fineStep (0 : Fin 3)) = g (observed 0) := h0
    _ = g (observed 2) := congrArg g equal_current_observation
    _ = observed (fineStep (2 : Fin 3)) := h2.symm

end PermanssonResearch.Quotient.Q01NonLumpable
