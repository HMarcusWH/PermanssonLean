import PermanssonResearch.ReverseSolver.TypedMenuCertification
import PermanssonResearch.ReverseSolver.CertificationExamples
import Mathlib.Tactic

/-!
# D0-E: true strategic interventions, finite candidate optimum, path values

All probability assertions here follow from the canonical typed process via
the new unconditional all-horizon path/value correspondence, rather than
simply postulating a rational/typed score bridge. Rational selection is fixed
for the entire horizon; these are not adaptive D1 policies.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace TypedMenuCertificationExamples

open TypedMenuCertification
open FiniteStrategicRealization
open FiniteStrategicPathBridge

noncomputable section

def twoTypedChoices :=
  typedFiniteMenu RationalExamples.halfGoalMatrix
    RationalExamples.twoRationalChoices

/-- For every horizon, state, and listed index, the rational and typed
canonical prefix-law probabilities are equal. -/
theorem two_choice_values_equal_all_horizons
    (T : ℕ) (x : Fin 2) (i : Bool) :
    (rationalMemberValue RationalExamples.twoRationalChoices
      RationalExamples.goalOne x T i : ℝ) =
    memberValue twoTypedChoices (typedTarget RationalExamples.goalOne)
      (decode x) T i := by
  exact
    (certifiedExactCorrespondence
      RationalExamples.halfGoalMatrix RationalExamples.twoRationalChoices
      RationalExamples.goalOne x T).exact_values i
        (by simp [RationalExamples.twoRationalChoices])

/-- The exact rational solver selects the full-goal strategic intervention
from the declared two-entry menu at the stated one-step query. -/
theorem selected_true :
    selectRationalMember RationalExamples.twoRationalChoices
      RationalExamples.goalOne (0 : Fin 2) 1 = true :=
  RationalExamples.selected_sure_one_step

theorem selected_typed_member :
    selectRationalMember RationalExamples.twoRationalChoices
      RationalExamples.goalOne (0 : Fin 2) 1 ∈ twoTypedChoices.indices :=
  certifiedSelected_mem
    RationalExamples.halfGoalMatrix RationalExamples.twoRationalChoices
    RationalExamples.goalOne (0 : Fin 2) 1

/-- A proved typed maximality statement, not just a rational-list
calculation: the chosen intervention dominates BOTH eligible actual
strategic-world alternatives on the canonical path event. -/
theorem selected_dominates_both_typed :
    ∀ j ∈ twoTypedChoices.indices,
      memberValue twoTypedChoices (typedTarget RationalExamples.goalOne)
        (decode (0 : Fin 2)) 1 j ≤
      memberValue twoTypedChoices (typedTarget RationalExamples.goalOne)
        (decode (0 : Fin 2)) 1
        (selectRationalMember RationalExamples.twoRationalChoices
          RationalExamples.goalOne (0 : Fin 2) 1) :=
  certifiedSelected_dominatesTyped
    RationalExamples.halfGoalMatrix RationalExamples.twoRationalChoices
    RationalExamples.goalOne (0 : Fin 2) 1

theorem selected_typed_value_one :
    memberValue twoTypedChoices (typedTarget RationalExamples.goalOne)
      (decode (0 : Fin 2)) 1
      (selectRationalMember RationalExamples.twoRationalChoices
        RationalExamples.goalOne (0 : Fin 2) 1) = 1 := by
  rw [selected_true]
  have h := two_choice_values_equal_all_horizons 1 (0 : Fin 2) true
  rw [RationalExamples.sure_one_step] at h
  norm_num at h
  exact h.symm

theorem selected_preserves_original_world :
    ((twoTypedChoices.choice
      (selectRationalMember RationalExamples.twoRationalChoices
        RationalExamples.goalOne (0 : Fin 2) 1)).intervention.apply.world) =
      (realizedModel RationalExamples.halfGoalMatrix).world :=
  certifiedSelected_preserves_world
    RationalExamples.halfGoalMatrix RationalExamples.twoRationalChoices
    RationalExamples.goalOne (0 : Fin 2) 1

theorem selected_preserves_original_update :
    ((twoTypedChoices.choice
      (selectRationalMember RationalExamples.twoRationalChoices
        RationalExamples.goalOne (0 : Fin 2) 1)).intervention.apply.generator.update) =
      (realizedModel RationalExamples.halfGoalMatrix).generator.update :=
  certifiedSelected_preserves_update
    RationalExamples.halfGoalMatrix RationalExamples.twoRationalChoices
    RationalExamples.goalOne (0 : Fin 2) 1

end
end TypedMenuCertificationExamples
end ReverseSolver
end PermanssonResearch
