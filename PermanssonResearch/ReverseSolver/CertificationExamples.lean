import PermanssonResearch.ReverseSolver.FiniteEvaluation
import PermanssonResearch.ReverseSolver.CertifiedSelection
import Mathlib.Tactic

/-!
# D0-B: exact finite rational witness

The frozen two-candidate list is [false, true]. On the two-state model,
the first candidate has 1/2 one-step goal probability and the second has
one-step goal probability 1. These arithmetic results are decided by Lean.
They are *not* assertions that these abstract matrices correspond to the
canonical kernels of the original typed interventions.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace RationalExamples

def halfGoalMatrix : RationalMarkovMatrix 2 where
  entry := fun y z =>
    if y = 0 then (1/2 : ℚ) else if z = 1 then 1 else 0
  entry_nonneg := by
    intro y z
    split_ifs <;> norm_num
  row_sum_one := by
    intro y
    fin_cases y <;> norm_num [Fin.sum_univ_two]

def sureGoalMatrix : RationalMarkovMatrix 2 where
  entry := fun _ z => if z = 1 then 1 else 0
  entry_nonneg := by
    intro y z
    split_ifs <;> norm_num
  row_sum_one := by
    intro y
    norm_num [Fin.sum_univ_two]

def goalOne : RationalHittingTarget 2 where
  goal := {1}
  forbidden := ∅
  disjoint := by simp

def twoRationalChoices : RationalMatrixMenu Bool 2 where
  items := [false, true]
  items_nonempty := by decide
  matrix := fun c => if c then sureGoalMatrix else halfGoalMatrix

theorem half_one_step :
    rationalMemberValue twoRationalChoices goalOne 0 1 false = 1/2 := by decide

theorem sure_one_step :
    rationalMemberValue twoRationalChoices goalOne 0 1 true = 1 := by decide

theorem selected_sure_one_step :
    selectRationalMember twoRationalChoices goalOne 0 1 = true := by decide

theorem selected_has_maximum_one_step :
    ∀ i ∈ twoRationalChoices.items,
      rationalMemberValue twoRationalChoices goalOne 0 1 i ≤
        rationalMemberValue twoRationalChoices goalOne 0 1
          (selectRationalMember twoRationalChoices goalOne 0 1) :=
  selectRationalMember_dominates twoRationalChoices goalOne 0 1

theorem forward_agrees_in_example (y : Fin 2) (T : ℕ) :
    rationalForwardEnumeration halfGoalMatrix goalOne T y =
      rationalHittingValue halfGoalMatrix goalOne T y :=
  rationalForwardEnumeration_eq_recursion halfGoalMatrix goalOne T y

end RationalExamples
end ReverseSolver
end PermanssonResearch
