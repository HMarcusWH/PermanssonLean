import PermanssonResearch.ReverseSolver.NonstationaryTypedHitting
import PermanssonResearch.ReverseSolver.NonstationaryExamples
import PermanssonResearch.ReverseSolver.BellmanExamples
import Mathlib.Tactic

/-!
# D1-C2: actual typed time-varying path-law regression witnesses

The time-dependent deadline example (start=0, goal=1, forbidden=2)
achieves 5/8 in two transitions, and different initial deadlines
select provably different first-step laws. The stationary special
case reduces to the pre-existing D1-A alpha/P/U finitePrefixLaw.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace NonstationaryTypedExamples

open Bellman
open BellmanExamples
open ControlledKernel
open FiniteStrategicRealization
open FiniteStrategicPathBridge
open Nonstationary
open NonstationaryTyped
open PermanssonLean.ProbabilitySupport

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- Actual typed strategic-world deadline-dependent probability is exactly
5/8, the same certified probability as the rational D1-C1 process. -/
theorem typed_deadline_success_five_eighths :
    typedSuccessProbability deadlineSystem deadlineSchedule
      deadlineTarget 2 (0 : Fin 3) =
        ENNReal.ofReal (5/8 : ℝ) := by
  rw [typed_successProbability_eq_rational]
  exact NonstationaryExamples.deadline_success_exact

/-- Typed stationary path laws do not change when the arbitrary original
deadline changes: they coincide with the original D1-A canonical law. -/
theorem typed_stationary_reduces_to_D1A
    {C : Type*} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (rho : StateFeedback sys)
    (D t : ℕ) (x : Fin n) :
    typedPrefixLaw sys (stationarySchedule rho) D x t =
      finitePrefixLaw (feedbackModel sys rho).inducedKernel
        (decode x) t :=
  typedPrefixLaw_stationary sys rho D t x

/-- The 1-step prefix of a deadline-2 run is genuinely different from
the full 1-step deadline-1 run, even in the TYPED strategic-world law.
The proof transports through exact path-measure equality, rather than
inventing a new typed event. -/
theorem typed_cross_deadline_prefix_ne :
    typedPrefixLaw deadlineSystem deadlineSchedule 2
      (0 : Fin 3) 1 ≠
    typedPrefixLaw deadlineSystem deadlineSchedule 1
      (0 : Fin 3) 1 := by
  intro h
  have hmap := congrArg
    (fun mu : Measure ((i : Finset.Iic 1) →
        PermanssonLean.JointState Unit (Fin 3)) =>
      mu.map (prefixEncode 1)) h
  rw [typed_prefixLaw_map, typed_prefixLaw_map] at hmap
  exact NonstationaryExamples.deadline_one_two_prefix_ne hmap

/-- The typed time-zero distribution has no phantom action or transition. -/
theorem typed_zero_is_point_mass :
    typedPrefixLaw deadlineSystem deadlineSchedule 2
      (0 : Fin 3) 0 =
        Measure.dirac (singletonPrefix (decode (0 : Fin 3))) :=
  typedPrefixLaw_zero deadlineSystem deadlineSchedule 2 (0 : Fin 3)

/-- Fixed primitive P: both deadline-2 and deadline-1 controllers use
the very same world law as the baseline, despite different alpha. -/
theorem deadline_world_primitive_invariant :
    (selectedModel deadlineSystem deadlineSchedule 2 0).world =
      (selectedModel deadlineSystem deadlineSchedule 1 0).world := by
  rw [selected_world_fixed, selected_world_fixed]

/-- Fixed strategic update U, independently of the selected deadline. -/
theorem deadline_update_primitive_invariant :
    (selectedModel deadlineSystem deadlineSchedule 2 0).generator.update =
      (selectedModel deadlineSystem deadlineSchedule 1 0).generator.update := by
  rw [selected_update_fixed, selected_update_fixed]

end NonstationaryTypedExamples
end ReverseSolver
end PermanssonResearch
