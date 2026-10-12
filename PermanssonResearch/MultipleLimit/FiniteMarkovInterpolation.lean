import PermanssonResearch.MultipleLimit.FiniteMarkovMartingaleStep
import Mathlib.Tactic

/-!
# C53-04 — deterministic bounded-increment time interpolation

This is the pathwise algebraic half of the martingale strong law. It
supplies a Lipschitz-in-time bound for arbitrary physical trajectories,
allowing convergence along square horizons to extend to all horizons.
No stochastic convergence or independence assumption appears here.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteMarkovInterpolation

open FiniteMarkovMartingaleStep

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [DecidableEq Y]
variable (K : ProbabilityTheory.Kernel Y Y)
variable [ProbabilityTheory.IsMarkovKernel K]

theorem partialSum_sub_eq_Ico (z : Y) (w : ℕ → Y)
    {s t : ℕ} (hst : s ≤ t) :
    partialSum K z t w - partialSum K z s w =
      ∑ i ∈ Finset.Ico s t, increment K z i w := by
  simpa only [partialSum, Finset.sum_Ico_eq_sub _ hst]

/-- The norm of the difference of any two centered sums is bounded by
the number of genuine transitions separating their horizons. -/
theorem partialSum_time_lipschitz (z : Y) (w : ℕ → Y)
    {s t : ℕ} (hst : s ≤ t) :
    |partialSum K z t w - partialSum K z s w| ≤
      ((t-s : ℕ) : ℝ) := by
  rw [partialSum_sub_eq_Ico K z w hst]
  calc
    |∑ i ∈ Finset.Ico s t, increment K z i w| ≤
      ∑ i ∈ Finset.Ico s t, |increment K z i w| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Ico s t, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact increment_bounded K z i w
    _ = ((t-s : ℕ) : ℝ) := by simp

end FiniteMarkovInterpolation
end MultipleLimit
end PermanssonResearch
