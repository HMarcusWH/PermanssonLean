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

end FiniteMarkovCentered
end MultipleLimit
end PermanssonResearch
