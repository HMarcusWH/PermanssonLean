import PermanssonResearch.ReverseSolver.HistoryTypedHitting
import PermanssonResearch.ReverseSolver.HistoryPolicyExamples
import PermanssonResearch.ReverseSolver.NonstationaryTypedExamples
import Mathlib.Tactic

/-!
# D1-D2: typed history-controlled adversarial regression witnesses

These are laws of the actual alpha/P/U-induced typed partialTraj process,
not tests of a surrogate rational state machine. Both reconvergent histories
have positive mass and select distinct controls at identical elapsed state.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependentTypedExamples

open HistoryDependentTyped HistoryDependent HistoryDependentExamples
open Bellman BellmanExamples ControlledKernel
open FiniteStrategicRealization FiniteStrategicPathBridge

/-- The original clock-dependent 5/8 example transports to the fully
typed history-controlled law with no change in event semantics. -/
theorem typed_history_deadline_five_eighths :
    typedSuccessProbability deadlineSystem
      (embedMarkov deadlineSystem deadlineSchedule)
      deadlineTarget 2 (0 : Fin 3) =
      ENNReal.ofReal (5/8 : ℝ) := by
  rw [typed_successProbability_eq_rational]
  exact embedded_deadline_five_eighths

/-- The history-dependent typed Bellman optimum on the 3-state benchmark
is exactly 5/8, not only an attainable probability for one schedule. -/
theorem typed_history_deadline_optimum_five_eighths :
    (∀ σ : HistoryPolicy deadlineSystem,
      typedSuccessProbability deadlineSystem σ deadlineTarget 2
        (0 : Fin 3) ≤ ENNReal.ofReal (5/8 : ℝ)) ∧
    (∃ σ : HistoryPolicy deadlineSystem,
      typedSuccessProbability deadlineSystem σ deadlineTarget 2
        (0 : Fin 3) = ENNReal.ofReal (5/8 : ℝ)) := by
  simpa only [deadline_bellman_optimum_five_eighths] using
    (typed_history_bellman_optimal_and_attained deadlineSystem
      deadlineTarget 2 (0 : Fin 3))

/-- The left reconvergent prefix (0,1,0) is genuinely reached with mass
1/2 in the constructed typed strategic-world process. -/
theorem typed_reconverge_left_mass :
    typedPrefixLaw reconvergeSystem reconvergePolicy 3
      (0 : Fin 5) 2 {prefixDecode 2 leftReturn} =
      ENNReal.ofReal (1/2 : ℝ) := by
  rw [typed_prefix_atom_transport]
  exact reconverge_left_mass

/-- The right reconvergent prefix (0,2,0) is also genuinely reached with
mass 1/2 at identical time and current state. -/
theorem typed_reconverge_right_mass :
    typedPrefixLaw reconvergeSystem reconvergePolicy 3
      (0 : Fin 5) 2 {prefixDecode 2 rightReturn} =
      ENNReal.ofReal (1/2 : ℝ) := by
  rw [typed_prefix_atom_transport]
  exact reconverge_right_mass

/-- The typed one-step kernel remembers left history and chooses Win. -/
theorem typed_reconverge_left_wins :
    typedHistoryStep reconvergeSystem reconvergePolicy 3 2
      (prefixDecode 2 leftReturn) {decode (3 : Fin 5)} = 1 := by
  rw [typedHistoryStep_decode_singleton, prefixEncode_prefixDecode]
  norm_num [HistoryDependent.selectedEntry, reconvergePolicy,
    reconvergeSystem, reconvergeMatrix, leftReturn, HistoryDependent.last]

/-- The typed one-step kernel remembers right history and chooses Lose,
although its last observed joint state is the SAME as in the left case. -/
theorem typed_reconverge_right_loses :
    typedHistoryStep reconvergeSystem reconvergePolicy 3 2
      (prefixDecode 2 rightReturn) {decode (4 : Fin 5)} = 1 := by
  rw [typedHistoryStep_decode_singleton, prefixEncode_prefixDecode]
  norm_num [HistoryDependent.selectedEntry, reconvergePolicy,
    reconvergeSystem, reconvergeMatrix, rightReturn, HistoryDependent.last]

end HistoryDependentTypedExamples
end ReverseSolver
end PermanssonResearch
