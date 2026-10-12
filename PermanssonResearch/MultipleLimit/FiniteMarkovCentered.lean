import PermanssonResearch.MultipleLimit.FiniteKernelRealBridge
import Mathlib.Tactic

/-!
# Lane C2 — true finite Markov centered transition increments

For an arbitrary genuine Markov kernel K on a finite measurable state
space, the real transition matrix has exact nonnegative stochastic rows.
Consequently the one-step centered indicator has conditional row mean ZERO
and is bounded in absolute value by one. Both statements hold for
irrational and periodic transition matrices.

This is the algebraic conditional-mean/boundedness foundation of the
Markov martingale SLLN. The all-time orthogonality, variance growth and
almost-sure normalized-residual theorem are *separate open obligations*;
no unproved martingale or iid assumption is introduced in this file.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteMarkovCentered

open FiniteKernelRealBridge

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y] [DecidableEq Y]
variable [MeasurableSingletonClass Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- A genuine one-step Markov singleton probability is at most one. -/
theorem realTransition_le_one (y z : Y) :
    realTransition K y z ≤ 1 := by
  classical
  calc
    realTransition K y z ≤
        ∑ x : Y, realTransition K y x :=
      Finset.single_le_sum
        (fun x hx => realTransition_nonneg K y x)
        (Finset.mem_univ z)
    _ = 1 := realTransition_row_sum K y

/-- The actual one-step centered indicator has absolute value at most one,
for every current state y, next state x and tested event {z}. -/
theorem centered_increment_abs_le_one (y x z : Y) :
    |(if x = z then (1 : ℝ) else 0) - realTransition K y z| ≤ 1 := by
  classical
  have hp0 := realTransition_nonneg K y z
  have hp1 := realTransition_le_one K y z
  by_cases h : x = z
  · simp only [if_pos h]
    rw [abs_of_nonneg (sub_nonneg.mpr hp1)]
    linarith
  · simp only [if_neg h, zero_sub, abs_neg, abs_of_nonneg hp0]
    exact hp1

/-- Exact conditional mean zero under each REAL atom of the
original Markov kernel. This proves the row identity from the
original K, not a guessed IID surrogate or rational approximation. -/
theorem centered_row_mean_zero (y z : Y) :
    (∑ x : Y,
      realTransition K y x *
        ((if x = z then (1 : ℝ) else 0) -
          realTransition K y z)) = 0 := by
  classical
  have hdelta :
      (∑ x : Y,
        realTransition K y x * (if x = z then (1 : ℝ) else 0)) =
          realTransition K y z := by
    simp
  calc
    (∑ x : Y,
        realTransition K y x *
          ((if x = z then (1 : ℝ) else 0) -
            realTransition K y z)) =
      (∑ x : Y, realTransition K y x *
        (if x = z then (1 : ℝ) else 0)) -
        (∑ x : Y, realTransition K y x) *
          realTransition K y z := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        rw [Finset.sum_mul]
    _ = realTransition K y z -
        (∑ x : Y, realTransition K y x) *
          realTransition K y z := by rw [hdelta]
    _ = 0 := by rw [realTransition_row_sum K y]; ring

/-- The conditional second moment of the genuine centered singleton
increment is at most one, uniformly in the current state. This is the
one-step L² bound required for the future pathwise martingale variance
calculation; cross-time orthogonality is NOT established by this theorem. -/
theorem centered_row_second_moment_le_one (y z : Y) :
    (∑ x : Y, realTransition K y x *
      (((if x = z then (1 : ℝ) else 0) -
        realTransition K y z) ^ 2)) ≤ 1 := by
  classical
  calc
    (∑ x : Y, realTransition K y x *
        (((if x = z then (1 : ℝ) else 0) -
          realTransition K y z) ^ 2)) ≤
      (∑ x : Y, realTransition K y x * 1) := by
        apply Finset.sum_le_sum
        intro x hx
        let d : ℝ :=
          (if x = z then (1 : ℝ) else 0) - realTransition K y z
        have hab : |d| ≤ 1 := centered_increment_abs_le_one K y x z
        have hdlo : -1 ≤ d := (abs_le.mp hab).1
        have hdhi : d ≤ 1 := (abs_le.mp hab).2
        have hprod :
            0 ≤ (1 - d) * (1 + d) :=
          mul_nonneg (by linarith) (by linarith)
        have hd2 : d ^ 2 ≤ 1 := by nlinarith
        exact mul_le_mul_of_nonneg_left hd2
          (realTransition_nonneg K y x)
    _ = 1 := by simpa only [mul_one] using realTransition_row_sum K y

end FiniteMarkovCentered
end MultipleLimit
end PermanssonResearch
