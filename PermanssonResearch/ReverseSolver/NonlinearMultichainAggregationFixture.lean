import PermanssonResearch.ReverseSolver.NonlinearBooleanClassFunctional
import PermanssonResearch.ReverseSolver.C11ReferenceExamples
import Mathlib.Tactic

/-!
D-09 independent physical-class identity and nonlinear-aggregation
negative fixture. These two statements are individually proved in the
existing C11/Boolean sources. The additional actual mixed-class entry-law
proof remains mandatory for full D-09 acceptance.
-/
namespace PermanssonResearch.ReverseSolver.NonlinearMultichainAggregationFixture
open PermanssonResearch.ReverseSolver.C11
open PermanssonResearch.ReverseSolver.C11.ReferenceExamples
open PermanssonResearch.ReverseSolver.NonlinearPeriodThree

theorem physically_distinct_classes_with_shared_descriptor :
    (referenceStationaryFamily twoAbsorbing).length = 2 ∧
      (referenceStationaryFamily twoAbsorbing).map (fun r =>
        ∑ x : Fin 2, r.weights x *
          (if (fun _ : Fin 2 => true) x then 1 else 0)) = [1,1] := by
  exact physical_classes_remain_distinct

theorem nonlinear_classwise_aggregation_not_barycenter :
    ((booleanRationalScore 0 + booleanRationalScore 1)/2 = (1/2:ℚ)) ∧
      (booleanRationalScore (1/2) = (5/6:ℚ)) :=
  classwise_barycenter_invalid

end PermanssonResearch.ReverseSolver.NonlinearMultichainAggregationFixture
