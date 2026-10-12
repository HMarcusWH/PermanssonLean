import PermanssonResearch.MultipleLimit.FiniteMarkovMartingaleStep
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# C53-03 — actual canonical centered-increment square moments

The finite matrix's rowwise second moment is already certified elsewhere.
This module additionally proves square-integrability and a true bound
under the original infinite canonical path measure. It works from the
pathwise |D_t|≤1 statement, without any independence assumption.
The later cross-time covariance cancellation is a separate obligation.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteMarkovMartingaleMoments

open FiniteCanonicalPath
open FiniteMarkovMartingaleStep

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [DecidableEq Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

theorem increment_sq_le_one (z : Y) (t : ℕ) (w : ℕ → Y) :
    (increment K z t w) ^ 2 ≤ 1 := by
  have hb := increment_bounded K z t w
  have h₁ : -1 ≤ increment K z t w := (abs_le.mp hb).1
  have h₂ : increment K z t w ≤ 1 := (abs_le.mp hb).2
  nlinarith [mul_nonneg (show 0 ≤ 1 - increment K z t w by linarith)
    (show 0 ≤ 1 + increment K z t w by linarith)]

theorem increment_sq_integrable (μ : ProbabilityMeasure Y)
    (z : Y) (t : ℕ) :
    Integrable (fun w : ℕ → Y => (increment K z t w) ^ 2)
      (canonicalPathLaw K μ.toMeasure) := by
  have hm : Measurable (fun w : ℕ → Y => (increment K z t w) ^ 2) :=
    ((increment_measurable_at K z t).mono
      ((pastFiltration (Y := Y)).le (t+1)) le_rfl).pow_const 2
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ (fun w => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact increment_sq_le_one K z t w)

/-- This expectation bound concerns the ACTUAL canonical infinite path
law, not merely a rowwise algebraic quantity. -/
theorem integral_increment_sq_le_one (μ : ProbabilityMeasure Y)
    (z : Y) (t : ℕ) :
    (∫ w, (increment K z t w) ^ 2 ∂canonicalPathLaw K μ.toMeasure) ≤
      1 := by
  calc
    (∫ w, (increment K z t w) ^ 2
        ∂canonicalPathLaw K μ.toMeasure) ≤
      (∫ _w : ℕ → Y, (1 : ℝ)
        ∂canonicalPathLaw K μ.toMeasure) := by
          exact integral_mono (increment_sq_integrable K μ z t)
            (integrable_const (1 : ℝ))
            (fun w => increment_sq_le_one K z t w)
    _ = 1 := by simp

end FiniteMarkovMartingaleMoments
end MultipleLimit
end PermanssonResearch
