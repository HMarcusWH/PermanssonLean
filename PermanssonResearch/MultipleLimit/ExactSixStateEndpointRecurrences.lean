import PermanssonResearch.MultipleLimit.ExactSixStateCanonical
import PermanssonResearch.MultipleLimit.ExactEndpointRecurrences
import Mathlib.Tactic

/-!
# C53-12 — exact six-state class-specific endpoint recurrences

The two endpoints are whole RECURRENT CLASSES, rather than individual
absorbers. These exact ℚ recurrences distinguish A={a0,a1} from
B={b0,b1}, which are separately closed despite one class having
period two and the other being aperiodic.

This is exact finite-horizon rational arithmetic. The next module
transports it through the true canonical alpha/P/U finite-prefix laws
and then takes increasing infinite event unions.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateEndpointRecurrences

open ReverseSolver
open ExactSixState
open ExactSixStateCanonical

def targetA : RationalHittingTarget 6 where
  goal := {2, 3}
  forbidden := ∅
  disjoint := by simp

def targetB : RationalHittingTarget 6 where
  goal := {4, 5}
  forbidden := ∅
  disjoint := by simp

theorem hitA_from_A (T : ℕ) :
    rationalHittingValue sixStateMatrix targetA T 2 = 1 ∧
    rationalHittingValue sixStateMatrix targetA T 3 = 1 := by
  cases T with
  | zero =>
      constructor <;> norm_num [rationalHittingValue_zero, targetA]
  | succ T =>
      constructor <;> norm_num [rationalHittingValue_succ, targetA]

theorem hitB_from_B (T : ℕ) :
    rationalHittingValue sixStateMatrix targetB T 4 = 1 ∧
    rationalHittingValue sixStateMatrix targetB T 5 = 1 := by
  cases T with
  | zero =>
      constructor <;> norm_num [rationalHittingValue_zero, targetB]
  | succ T =>
      constructor <;> norm_num [rationalHittingValue_succ, targetB]

theorem hitA_from_B_zero (T : ℕ) :
    rationalHittingValue sixStateMatrix targetA T 4 = 0 ∧
    rationalHittingValue sixStateMatrix targetA T 5 = 0 := by
  induction T with
  | zero =>
      constructor <;> norm_num [rationalHittingValue_zero, targetA]
  | succ T ih =>
      constructor
      · rw [rationalHittingValue_succ]
        change (∑ z : Fin 6, transition 4 z *
          rationalHittingValue sixStateMatrix targetA T z) = 0
        norm_num [transition, Fin.sum_univ_succ, ih.1, ih.2]
      · rw [rationalHittingValue_succ]
        change (∑ z : Fin 6, transition 5 z *
          rationalHittingValue sixStateMatrix targetA T z) = 0
        norm_num [transition, Fin.sum_univ_succ, ih.1, ih.2]

theorem hitB_from_A_zero (T : ℕ) :
    rationalHittingValue sixStateMatrix targetB T 2 = 0 ∧
    rationalHittingValue sixStateMatrix targetB T 3 = 0 := by
  induction T with
  | zero =>
      constructor <;> norm_num [rationalHittingValue_zero, targetB]
  | succ T ih =>
      constructor
      · rw [rationalHittingValue_succ]
        change (∑ z : Fin 6, transition 2 z *
          rationalHittingValue sixStateMatrix targetB T z) = 0
        norm_num [transition, Fin.sum_univ_succ, ih.1, ih.2]
      · rw [rationalHittingValue_succ]
        change (∑ z : Fin 6, transition 3 z *
          rationalHittingValue sixStateMatrix targetB T z) = 0
        norm_num [transition, Fin.sum_univ_succ, ih.1, ih.2]

theorem hitA_from_u_succ (T : ℕ) :
    rationalHittingValue sixStateMatrix targetA (T+1) 1 =
      (1/2 : ℚ) * rationalHittingValue sixStateMatrix targetA T 1 +
        1/6 := by
  rw [rationalHittingValue_succ]
  change (∑ z : Fin 6, transition 1 z *
      rationalHittingValue sixStateMatrix targetA T z) =
    (1/2 : ℚ) * rationalHittingValue sixStateMatrix targetA T 1 + 1/6
  have ha := hitA_from_A T
  have hb := hitA_from_B_zero T
  norm_num [transition, Fin.sum_univ_succ, ha.1, ha.2, hb.1, hb.2]
  ring

theorem hitB_from_u_succ (T : ℕ) :
    rationalHittingValue sixStateMatrix targetB (T+1) 1 =
      (1/2 : ℚ) * rationalHittingValue sixStateMatrix targetB T 1 +
        1/3 := by
  rw [rationalHittingValue_succ]
  change (∑ z : Fin 6, transition 1 z *
      rationalHittingValue sixStateMatrix targetB T z) =
    (1/2 : ℚ) * rationalHittingValue sixStateMatrix targetB T 1 + 1/3
  have ha := hitB_from_A_zero T
  have hb := hitB_from_B T
  norm_num [transition, Fin.sum_univ_succ, ha.1, ha.2, hb.1, hb.2]
  ring

theorem hitA_from_u_closed (T : ℕ) :
    rationalHittingValue sixStateMatrix targetA T 1 =
      (1/3 : ℚ) * (1 - (1/2 : ℚ)^T) := by
  induction T with
  | zero => norm_num [rationalHittingValue_zero, targetA]
  | succ T ih =>
      rw [hitA_from_u_succ, ih, pow_succ]
      ring

theorem hitB_from_u_closed (T : ℕ) :
    rationalHittingValue sixStateMatrix targetB T 1 =
      (2/3 : ℚ) * (1 - (1/2 : ℚ)^T) := by
  induction T with
  | zero => norm_num [rationalHittingValue_zero, targetB]
  | succ T ih =>
      rw [hitB_from_u_succ, ih, pow_succ]
      ring

theorem hitA_from_t_closed (T : ℕ) :
    rationalHittingValue sixStateMatrix targetA (T+1) 0 =
      (1/3 : ℚ) * (1 - (1/2 : ℚ)^T) := by
  rw [rationalHittingValue_succ]
  change (∑ z : Fin 6, transition 0 z *
      rationalHittingValue sixStateMatrix targetA T z) = _
  norm_num [transition, Fin.sum_univ_succ]
  exact hitA_from_u_closed T

theorem hitB_from_t_closed (T : ℕ) :
    rationalHittingValue sixStateMatrix targetB (T+1) 0 =
      (2/3 : ℚ) * (1 - (1/2 : ℚ)^T) := by
  rw [rationalHittingValue_succ]
  change (∑ z : Fin 6, transition 0 z *
      rationalHittingValue sixStateMatrix targetB T z) = _
  norm_num [transition, Fin.sum_univ_succ]
  exact hitB_from_u_closed T

end ExactSixStateEndpointRecurrences
end MultipleLimit
end PermanssonResearch
