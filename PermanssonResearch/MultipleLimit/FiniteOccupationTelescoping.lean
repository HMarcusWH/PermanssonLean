import PermanssonResearch.MultipleLimit.FiniteCesaroAlgebra
import Mathlib.Tactic

/-!
# Lane C2 — exact pathwise occupation / martingale telescoping

The canonical finite-chain martingale residual is the difference between
the NEXT state's indicator and the conditional transition probability.
For ANY infinite word w and ANY transition array K, the cumulative
expected occupation drift equals the two bounded endpoint indicators
MINUS the cumulative residual.

This algebra is pointwise and unconditional: it neither assumes iid
observations nor asserts that the residual is a martingale. The
canonical conditional-mean-zero and strong-law stages are separate.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteOccupationTelescoping

variable {Y : Type*}

def indicatorAt (w : ℕ → Y) (z : Y) (t : ℕ) : ℝ :=
  if w t = z then 1 else 0

/-- The exact next-state minus K-conditional-mean residual. -/
def transitionResidual (K : Y → Y → ℝ)
    (w : ℕ → Y) (z : Y) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T,
    (indicatorAt w z (t+1) - K (w t) z)

/-- The finite unscaled invariance defect: sum of K-conditioned
next-state probabilities minus empirical current-state counts. -/
def occupationDrift (K : Y → Y → ℝ)
    (w : ℕ → Y) (z : Y) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, K (w t) z) -
    (∑ t ∈ Finset.range T, indicatorAt w z t)

/-- EXACT pathwise telescoping at every time horizon, including T=0.
No Markov or conditional independence assumption appears in the lemma. -/
theorem occupationDrift_telescope (K : Y → Y → ℝ)
    (w : ℕ → Y) (z : Y) (T : ℕ) :
    occupationDrift K w z T =
      indicatorAt w z T - indicatorAt w z 0 -
        transitionResidual K w z T := by
  classical
  have htel :
      (∑ t ∈ Finset.range T,
        (indicatorAt w z (t+1) - indicatorAt w z t)) =
        indicatorAt w z T - indicatorAt w z 0 := by
    exact Finset.sum_range_sub (fun n => indicatorAt w z n) T
  unfold occupationDrift transitionResidual
  calc
    (∑ t ∈ Finset.range T, K (w t) z) -
        (∑ t ∈ Finset.range T, indicatorAt w z t) =
        (∑ t ∈ Finset.range T,
          (indicatorAt w z (t+1) - indicatorAt w z t)) -
        (∑ t ∈ Finset.range T,
          (indicatorAt w z (t+1) - K (w t) z)) := by
      simp_rw [Finset.sum_sub_distrib]
      ring
    _ = indicatorAt w z T - indicatorAt w z 0 -
        (∑ t ∈ Finset.range T,
          (indicatorAt w z (t+1) - K (w t) z)) := by
      rw [htel]

/-- Indicators are exactly zero or one, so their endpoint difference
is bounded by one at ALL horizons and physical sample paths. -/
theorem indicatorAt_diff_abs_le_one
    (w : ℕ → Y) (z : Y) (s t : ℕ) :
    |indicatorAt w z t - indicatorAt w z s| ≤ 1 := by
  classical
  unfold indicatorAt
  split_ifs <;> norm_num

theorem indicatorAt_nonneg (w : ℕ → Y) (z : Y) (t : ℕ) :
    0 ≤ indicatorAt w z t := by
  classical
  unfold indicatorAt
  split_ifs <;> norm_num

theorem indicatorAt_le_one (w : ℕ → Y) (z : Y) (t : ℕ) :
    indicatorAt w z t ≤ 1 := by
  classical
  unfold indicatorAt
  split_ifs <;> norm_num

/-- The exact finite-horizon estimate the eventual martingale
SLLN will need: after dividing by a positive horizon, the
remaining deterministic endpoint error has magnitude at most 1/T. -/
theorem occupationDrift_residual_error_bound
    (K : Y → Y → ℝ) (w : ℕ → Y)
    (z : Y) (T : ℕ) (hT : 0 < T) :
    |(((T : ℝ)⁻¹) * occupationDrift K w z T) +
      (((T : ℝ)⁻¹) * transitionResidual K w z T)| ≤
      ((T : ℝ)⁻¹) := by
  have hbound := indicatorAt_diff_abs_le_one w z 0 T
  rw [occupationDrift_telescope]
  have hTpos : 0 ≤ ((T : ℝ)⁻¹) := by positivity
  have hs :
      ((T : ℝ)⁻¹) *
        (indicatorAt w z T - indicatorAt w z 0 -
          transitionResidual K w z T) +
        ((T : ℝ)⁻¹) * transitionResidual K w z T =
      ((T : ℝ)⁻¹) *
        (indicatorAt w z T - indicatorAt w z 0) := by ring
  rw [hs, abs_mul, abs_of_nonneg hTpos]
  exact (mul_le_mul_of_nonneg_left hbound hTpos).trans
    (by simp)

end FiniteOccupationTelescoping
end MultipleLimit
end PermanssonResearch
