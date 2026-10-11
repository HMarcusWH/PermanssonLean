import PermanssonResearch.MultipleLimit.ExactRationalAbsorption
import Mathlib.Tactic

/-!
# Lane C1 — separate exact destination-hitting recurrences

Unlike absorption into the union {a,b}, these two independently certified
rational objectives distinguish which absorbing state was first reached.
Terminal probabilities are not assumed and finite times include time zero.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactEndpointRecurrences

open ReverseSolver ExactRationalAbsorption

def aTarget : RationalHittingTarget 4 where
  goal := {2}
  forbidden := ∅
  disjoint := by simp

def bTarget : RationalHittingTarget 4 where
  goal := {3}
  forbidden := ∅
  disjoint := by simp

theorem hit_a_from_a (T : ℕ) :
    rationalHittingValue fourStateMatrix aTarget T 2 = 1 := by
  cases T with
  | zero => norm_num [rationalHittingValue_zero, aTarget]
  | succ n => norm_num [rationalHittingValue_succ, aTarget]

theorem hit_a_from_b (T : ℕ) :
    rationalHittingValue fourStateMatrix aTarget T 3 = 0 := by
  induction T with
  | zero => norm_num [rationalHittingValue_zero, aTarget]
  | succ n ih =>
      rw [rationalHittingValue_succ]
      change (∑ z : Fin 4, fourStateMatrix.entry 3 z *
        rationalHittingValue fourStateMatrix aTarget n z) = 0
      rw [Fin.sum_univ_four]
      norm_num [fourStateMatrix, ih]

theorem hit_b_from_b (T : ℕ) :
    rationalHittingValue fourStateMatrix bTarget T 3 = 1 := by
  cases T with
  | zero => norm_num [rationalHittingValue_zero, bTarget]
  | succ n => norm_num [rationalHittingValue_succ, bTarget]

theorem hit_b_from_a (T : ℕ) :
    rationalHittingValue fourStateMatrix bTarget T 2 = 0 := by
  induction T with
  | zero => norm_num [rationalHittingValue_zero, bTarget]
  | succ n ih =>
      rw [rationalHittingValue_succ]
      change (∑ z : Fin 4, fourStateMatrix.entry 2 z *
        rationalHittingValue fourStateMatrix bTarget n z) = 0
      rw [Fin.sum_univ_four]
      norm_num [fourStateMatrix, ih]

theorem hit_a_from_u_succ (T : ℕ) :
    rationalHittingValue fourStateMatrix aTarget (T + 1) 1 =
      (1/2 : ℚ) * rationalHittingValue fourStateMatrix aTarget T 1 +
        1/6 := by
  rw [rationalHittingValue_succ]
  change (∑ z : Fin 4, fourStateMatrix.entry 1 z *
      rationalHittingValue fourStateMatrix aTarget T z) =
    (1/2 : ℚ) * rationalHittingValue fourStateMatrix aTarget T 1 + 1/6
  rw [Fin.sum_univ_four]
  simp only [hit_a_from_a T, hit_a_from_b T]
  norm_num [fourStateMatrix] <;> ring

theorem hit_b_from_u_succ (T : ℕ) :
    rationalHittingValue fourStateMatrix bTarget (T + 1) 1 =
      (1/2 : ℚ) * rationalHittingValue fourStateMatrix bTarget T 1 +
        1/3 := by
  rw [rationalHittingValue_succ]
  change (∑ z : Fin 4, fourStateMatrix.entry 1 z *
      rationalHittingValue fourStateMatrix bTarget T z) =
    (1/2 : ℚ) * rationalHittingValue fourStateMatrix bTarget T 1 + 1/3
  rw [Fin.sum_univ_four]
  simp only [hit_b_from_b T, hit_b_from_a T]
  norm_num [fourStateMatrix] <;> ring

theorem hit_a_from_u_closed (T : ℕ) :
    rationalHittingValue fourStateMatrix aTarget T 1 =
      (1/3 : ℚ) * (1 - (1/2 : ℚ)^T) := by
  induction T with
  | zero => norm_num [rationalHittingValue_zero, aTarget]
  | succ T ih =>
      rw [hit_a_from_u_succ, ih, pow_succ]
      ring

theorem hit_b_from_u_closed (T : ℕ) :
    rationalHittingValue fourStateMatrix bTarget T 1 =
      (2/3 : ℚ) * (1 - (1/2 : ℚ)^T) := by
  induction T with
  | zero => norm_num [rationalHittingValue_zero, bTarget]
  | succ T ih =>
      rw [hit_b_from_u_succ, ih, pow_succ]
      ring

theorem hit_a_from_t_succ (T : ℕ) :
    rationalHittingValue fourStateMatrix aTarget (T + 1) 0 =
      rationalHittingValue fourStateMatrix aTarget T 1 := by
  rw [rationalHittingValue_succ]
  change (∑ z : Fin 4, fourStateMatrix.entry 0 z *
      rationalHittingValue fourStateMatrix aTarget T z) =
    rationalHittingValue fourStateMatrix aTarget T 1
  rw [Fin.sum_univ_four]
  norm_num [fourStateMatrix]

theorem hit_b_from_t_succ (T : ℕ) :
    rationalHittingValue fourStateMatrix bTarget (T + 1) 0 =
      rationalHittingValue fourStateMatrix bTarget T 1 := by
  rw [rationalHittingValue_succ]
  change (∑ z : Fin 4, fourStateMatrix.entry 0 z *
      rationalHittingValue fourStateMatrix bTarget T z) =
    rationalHittingValue fourStateMatrix bTarget T 1
  rw [Fin.sum_univ_four]
  norm_num [fourStateMatrix]

theorem hit_a_from_t_closed (T : ℕ) :
    rationalHittingValue fourStateMatrix aTarget (T + 1) 0 =
      (1/3 : ℚ) * (1 - (1/2 : ℚ)^T) := by
  rw [hit_a_from_t_succ, hit_a_from_u_closed]

theorem hit_b_from_t_closed (T : ℕ) :
    rationalHittingValue fourStateMatrix bTarget (T + 1) 0 =
      (2/3 : ℚ) * (1 - (1/2 : ℚ)^T) := by
  rw [hit_b_from_t_succ, hit_b_from_u_closed]

end ExactEndpointRecurrences
end MultipleLimit
end PermanssonResearch
