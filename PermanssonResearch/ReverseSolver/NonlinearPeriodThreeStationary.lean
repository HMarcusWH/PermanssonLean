import PermanssonResearch.ReverseSolver.NonlinearPeriodThreePathLaw
import PermanssonLean.Regime.Occupation
import Mathlib.Tactic

/-!
Native three-phase occupation witness. This certifies the real alpha-P-U
orbit and an explicit normalized candidate cycle law. Equality to the
canonical selected stationary law is NOT silently inferred.
-/
open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.ReverseSolver.NonlinearPeriodThree
open PermanssonLean
open PermanssonLean.RegimeSpecification

def canonicalCycleState (i : Phase) : State := (i, i != 0)

theorem native_cycle_state_zero : canonicalCycleState 0 = start := by decide
theorem native_cycle_state_one : canonicalCycleState 1 = (1,true) := by decide
theorem native_cycle_state_two : canonicalCycleState 2 = (2,true) := by decide

theorem native_cycle_successor (i : Phase) :
    nextState phaseAwarePolicy (canonicalCycleState i) =
      canonicalCycleState (i+1) := by
  fin_cases i <;> decide

def phaseIndex : ℕ → Phase
  | 0 => 0
  | n+1 => phaseIndex n + 1

theorem native_phase_orbit_is_cycle (n : ℕ) :
    nativeOrbit phaseAwarePolicy n = canonicalCycleState (phaseIndex n) := by
  induction n with
  | zero => exact native_cycle_state_zero.symm
  | succ n ih =>
      rw [nativeOrbit, phaseIndex, ih]
      exact native_cycle_successor (phaseIndex n)

noncomputable def exactCycleLaw : ProbabilityMeasure State :=
  (uniformFinProbability 3 (by norm_num)).map canonicalCycleState

theorem native_three_phase_true_share :
    ((if (canonicalCycleState 0).2 then (1:ℚ) else 0) +
      (if (canonicalCycleState 1).2 then (1:ℚ) else 0) +
      (if (canonicalCycleState 2).2 then (1:ℚ) else 0))/3 = 2/3 := by
  norm_num [canonicalCycleState]

end PermanssonResearch.ReverseSolver.NonlinearPeriodThree
