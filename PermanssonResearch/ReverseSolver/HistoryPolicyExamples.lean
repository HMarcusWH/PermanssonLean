import PermanssonResearch.ReverseSolver.HistoryBellmanDominance
import PermanssonResearch.ReverseSolver.NonstationaryExamples
import Mathlib.Tactic

/-!
# D1-D1: exact regression of D1-B/C1 benchmark through history embedding

A genuinely history-sensitive reachable-prefix witness and the universal
history-policy Bellman inequality remain subsequent proof obligations.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependentExamples

open HistoryDependent
open Bellman
open BellmanExamples
open ControlledKernel

/-- The original deadline-two 5/8 strategy is a valid history controller,
with the genuine new partialTraj probability exactly equal to 5/8. -/
theorem embedded_deadline_five_eighths :
    successProbability BellmanExamples.deadlineSystem
      (embedMarkov BellmanExamples.deadlineSystem BellmanExamples.deadlineSchedule)
      BellmanExamples.deadlineTarget 2 (0 : Fin 3) =
        ENNReal.ofReal (5/8 : ℝ) := by
  rw [successProbability_embedMarkov]
  exact NonstationaryExamples.deadline_success_exact

end HistoryDependentExamples
end ReverseSolver
end PermanssonResearch
