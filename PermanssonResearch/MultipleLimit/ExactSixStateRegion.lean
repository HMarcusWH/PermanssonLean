import PermanssonResearch.MultipleLimit.ExactSixState
import Mathlib.Tactic

/-!
# Lane C2 — proper six-state candidate region and frozen observation

The proper physical region B = {u, a0, a1, b0, b1} is closed under
the ACTUAL six-state rational transition matrix. The declared descriptor
distinguishes the transient state u from recurrent states, while assigning
both recurrent classes the same observed code.

These are exact finite kernel/descriptor facts preparing a later original
Exact GR recovery witness. Neither empirical occupation convergence nor
an Exact GR certificate is asserted here.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateRegion

open ExactSixState

/-- The exact proper region excludes only the initial transient t. -/
def region : Set (Fin 6) := {i | i ≠ 0}

/-- A nontrivial proper region containing a transient and recurrent states. -/
theorem region_proper_and_nonempty :
    (1 : Fin 6) ∈ region ∧ (0 : Fin 6) ∉ region := by
  decide

/-- No positive one-step transition exits B, proved against the genuine
six-state row-stochastic rational matrix, not merely inferred from a graph. -/
theorem region_closed :
    ∀ i j : Fin 6,
      i ∈ region → 0 < transition i j → j ∈ region := by
  decide

/-- Both stationary class candidates live entirely inside the proper
region; this does not assume any occupation-limit theorem. -/
theorem recurrent_support_in_region :
    classA ⊆ region ∧ classB ⊆ region := by
  constructor
  · intro i hi
    fin_cases i <;> norm_num [classA, region] at *
  · intro i hi
    fin_cases i <;> norm_num [classB, region] at *

/-- The frozen descriptor remains nonconstant on the candidate region. -/
theorem region_descriptor_nondegenerate :
    (1 : Fin 6) ∈ region ∧ (2 : Fin 6) ∈ region ∧
      observedRecurrent 1 ≠ observedRecurrent 2 := by
  decide

/-- Both physically distinct recurrent classes have the same observed
descriptor value, but the proper region retains a distinct transient code. -/
theorem recurrent_descriptor_collapse :
    (∀ i ∈ classA, observedRecurrent i = true) ∧
    (∀ i ∈ classB, observedRecurrent i = true) := by
  constructor <;> intro i hi <;> fin_cases i <;>
    norm_num [classA, classB, observedRecurrent] at *

end ExactSixStateRegion
end MultipleLimit
end PermanssonResearch
