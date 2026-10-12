import PermanssonResearch.MultipleLimit.FiniteOccupationTelescoping
import PermanssonResearch.MultipleLimit.FiniteCesaroAlgebra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Lane C2 — exact normalized finite-state empirical vector algebra

Empirical vector at strictly positive horizon n+1:
  v_n(j) = 1/(n+1) * #{t<n+1 : w_t=j}.

The transition pushforward of this physical occupation vector
equals the time average of the genuine kernel's next-state
probabilities. The exact defect equals the pathwise centered
martingale residual plus the bounded endpoint discrepancy.

Every finite-horizon empirical vector is normalized. This file
does not assert a.s. residual convergence; the Markov martingale
strong law is the remaining independent probabilistic input.
-/

open Filter
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteOccupationVector

open FiniteOccupationTelescoping
open FiniteCesaroAlgebra

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

noncomputable def empiricalVector
    (w : ℕ → Y) (n : ℕ) (j : Y) : ℝ :=
  (((n+1 : ℕ) : ℝ)⁻¹) *
    (∑ t ∈ Finset.range (n+1), indicatorAt w j t)

theorem empiricalVector_nonneg (w : ℕ → Y) (n : ℕ) (j : Y) :
    0 ≤ empiricalVector w n j := by
  unfold empiricalVector
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro t ht
  exact indicatorAt_nonneg w j t

theorem sum_indicatorAt (w : ℕ → Y) (t : ℕ) :
    (∑ j : Y, indicatorAt w j t) = 1 := by
  simp [indicatorAt]

theorem empiricalVector_total (w : ℕ → Y) (n : ℕ) :
    (∑ j : Y, empiricalVector w n j) = 1 := by
  classical
  calc
    (∑ j : Y, empiricalVector w n j) =
      (((n+1 : ℕ) : ℝ)⁻¹) *
        (∑ t ∈ Finset.range (n+1),
          ∑ j : Y, indicatorAt w j t) := by
      simp only [empiricalVector, ← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    _ = (((n+1 : ℕ) : ℝ)⁻¹) *
        (((n+1 : ℕ) : ℝ)) := by
      simp_rw [sum_indicatorAt w]
      simp
    _ = 1 := inv_mul_cancel₀ (by positivity)

theorem pushVector_empirical
    (K : Y → Y → ℝ) (w : ℕ → Y) (n : ℕ) (z : Y) :
    pushVector K (empiricalVector w n) z =
      (((n+1 : ℕ) : ℝ)⁻¹) *
        (∑ t ∈ Finset.range (n+1), K (w t) z) := by
  classical
  unfold pushVector empiricalVector
  calc
    (∑ i : Y,
        (((n+1 : ℕ) : ℝ)⁻¹) *
          (∑ t ∈ Finset.range (n+1), indicatorAt w i t) *
            K i z) =
      (((n+1 : ℕ) : ℝ)⁻¹) *
        (∑ i : Y, ∑ t ∈ Finset.range (n+1),
          indicatorAt w i t * K i z) := by
      simp_rw [mul_assoc]
      rw [Finset.mul_sum]
      congr 1
      funext i
      rw [Finset.sum_mul]
    _ = (((n+1 : ℕ) : ℝ)⁻¹) *
        (∑ t ∈ Finset.range (n+1), ∑ i : Y,
          indicatorAt w i t * K i z) := by
      rw [Finset.sum_comm]
    _ = (((n+1 : ℕ) : ℝ)⁻¹) *
        (∑ t ∈ Finset.range (n+1), K (w t) z) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      simp [indicatorAt]

theorem empiricalVector_stationarity_defect
    (K : Y → Y → ℝ) (w : ℕ → Y) (n : ℕ) (z : Y) :
    pushVector K (empiricalVector w n) z -
      empiricalVector w n z =
        (((n+1 : ℕ) : ℝ)⁻¹) *
          occupationDrift K w z (n+1) := by
  rw [pushVector_empirical]
  unfold empiricalVector occupationDrift
  ring

theorem empiricalVector_stationarity_defect_bound
    (K : Y → Y → ℝ) (w : ℕ → Y) (n : ℕ) (z : Y) :
    |(pushVector K (empiricalVector w n) z -
       empiricalVector w n z) +
      (((n+1 : ℕ) : ℝ)⁻¹) *
        transitionResidual K w z (n+1)| ≤
      (((n+1 : ℕ) : ℝ)⁻¹) := by
  rw [empiricalVector_stationarity_defect]
  exact occupationDrift_residual_error_bound K w z (n+1)
    (Nat.succ_pos n)

end FiniteOccupationVector
end MultipleLimit
end PermanssonResearch
