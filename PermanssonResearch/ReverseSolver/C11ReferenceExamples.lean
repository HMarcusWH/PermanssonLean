import PermanssonResearch.ReverseSolver.C11ReferenceStationaryFamily

namespace PermanssonResearch.ReverseSolver.C11.ReferenceExamples

open C11

def periodic : RationalMarkovMatrix 2 where
  entry x y := if x=y then 0 else 1
  entry_nonneg x y := by split_ifs <;> norm_num
  row_sum_one x := by fin_cases x <;> norm_num [Fin.sum_univ_two]

def nearlyReducible : RationalMarkovMatrix 2 where
  entry x y := if x=y then 999/1000 else 1/1000
  entry_nonneg x y := by split_ifs <;> norm_num
  row_sum_one x := by fin_cases x <;> norm_num [Fin.sum_univ_two]

def twoAbsorbing : RationalMarkovMatrix 2 where
  entry x y := if x=y then 1 else 0
  entry_nonneg x y := by split_ifs <;> norm_num
  row_sum_one x := by simp [eq_comm]

theorem periodic_reference_exact :
    (referenceStationaryFamily periodic).map
      (fun r => [r.weights 0,r.weights 1])=[[(1/2:ℚ),1/2]] := by
  decide +kernel

theorem nearly_reducible_reference_exact :
    (referenceStationaryFamily nearlyReducible).map
      (fun r => [r.weights 0,r.weights 1])=[[(1/2:ℚ),1/2]] := by
  decide +kernel

/-- Equal descriptor labels do not merge distinct physical bottom classes. -/
theorem physical_classes_remain_distinct :
    (referenceStationaryFamily twoAbsorbing).length=2 ∧
      (referenceStationaryFamily twoAbsorbing).map (fun r =>
        ∑ x : Fin 2, r.weights x*(if (fun _ : Fin 2 => true) x then 1 else 0))=[1,1] := by
  decide +kernel

def corruptedPeriodic : ClassStationaryCandidate 2 where
  classStates := {0,1}
  weights x := if x=0 then 1/3 else 2/3

theorem corrupted_stationary_receipt_rejected :
    checkClassStationary periodic corruptedPeriodic=false := by decide +kernel

theorem periodic_family_accepted : checkStationaryFamily periodic
    (referenceStationaryFamily periodic)=true := referenceStationaryFamily_check periodic

def empty : RationalMarkovMatrix 0 where
  entry x _ := Fin.elim0 x
  entry_nonneg x _ := Fin.elim0 x
  row_sum_one x := Fin.elim0 x

theorem zero_dimension_reference_rejected : checkStationaryFamily empty
    (referenceStationaryFamily empty)=false :=
  checkStationaryFamily_zero_rejected empty (referenceStationaryFamily empty)

end PermanssonResearch.ReverseSolver.C11.ReferenceExamples
