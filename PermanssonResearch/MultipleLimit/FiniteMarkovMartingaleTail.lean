import PermanssonResearch.MultipleLimit.FiniteMarkovMartingaleVariance
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# C53-04 — finite-horizon canonical martingale concentration

This file turns the proved orthogonal, bounded canonical innovations into
an unconditional second-moment tail estimate on the original infinite-path
measure, for every finite state, initial probability law, and horizon.

The tail estimate does NOT alone prove the almost-sure SLLN: summability
along a sparse sequence and a genuine time-interpolation argument are
required in subsequent proofs.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteMarkovMartingaleTail

open FiniteCanonicalPath
open FiniteMarkovMartingaleStep
open FiniteMarkovMartingale
open FiniteMarkovMartingaleVariance

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [StandardBorelSpace Y]
variable [Nonempty Y] [DecidableEq Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- Conditional centering implies a genuinely zero unconditional mean
for each Markov innovation. -/
theorem integral_increment_zero
    (μ : ProbabilityMeasure Y) (z : Y) (t : ℕ) :
    (∫ w, increment K z t w ∂canonicalPathLaw K μ.toMeasure) = 0 := by
  let P := canonicalPathLaw K μ.toMeasure
  calc
    (∫ w, increment K z t w ∂P) =
      ∫ w, (condExp (pastFiltration (Y := Y) t) P
        (increment K z t)) w ∂P := by
          exact (integral_condExp ((pastFiltration (Y := Y)).le t)).symm
    _ = 0 := by
      rw [integral_congr_ae (centered_increment_condExp_zero K μ z t)]
      simp

/-- The partial centered sum has mean zero under arbitrary initial
probability, without assuming the starting chain is stationary. -/
theorem integral_partialSum_zero
    (μ : ProbabilityMeasure Y) (z : Y) (T : ℕ) :
    (∫ w, partialSum K z T w ∂canonicalPathLaw K μ.toMeasure) = 0 := by
  let P := canonicalPathLaw K μ.toMeasure
  induction T with
  | zero =>
      simp [partialSum_zero]
  | succ t ih =>
      have hpath :
          (fun w : ℕ → Y => partialSum K z (t+1) w) =
            (fun w => partialSum K z t w + increment K z t w) := by
        funext w
        exact partialSum_succ K z t w
      change (∫ w, partialSum K z (t+1) w ∂P) = 0
      rw [show (fun w : ℕ → Y => partialSum K z (t+1) w) =
          (fun w => partialSum K z t w + increment K z t w) from hpath]
      rw [integral_add (partialSum_integrable K μ z t)
        (increment_integrable K μ z t)]
      change (∫ w, partialSum K z t w ∂P) +
        (∫ w, increment K z t w ∂P) = 0
      rw [ih, integral_increment_zero K μ z t]
      ring

/-- Square integrability as an actual Mathlib L² property, needed
to apply the real Chebyshev inequality. -/
theorem partialSum_memLp_two
    (μ : ProbabilityMeasure Y) (z : Y) (T : ℕ) :
    MemLp (partialSum K z T) 2
      (canonicalPathLaw K μ.toMeasure) := by
  have hm : AEStronglyMeasurable (partialSum K z T)
      (canonicalPathLaw K μ.toMeasure) :=
    ((partialSum_measurable_at K z T).mono
      ((pastFiltration (Y := Y)).le T) le_rfl).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hm).2
    (partialSum_sq_integrable K μ z T)

/-- Honest finite-time Chebyshev estimate for the original canonical
Markov path law. The denominator is a positive REAL threshold squared. -/
theorem partialSum_tail_le_time
    (μ : ProbabilityMeasure Y) (z : Y)
    (T : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (canonicalPathLaw K μ.toMeasure)
      {w : ℕ → Y | ε ≤ |partialSum K z T w|} ≤
        ENNReal.ofReal ((T : ℝ) / ε ^ 2) := by
  let P := canonicalPathLaw K μ.toMeasure
  have hmem := partialSum_memLp_two K μ z T
  have hvar : variance (partialSum K z T) P ≤ (T : ℝ) :=
    (variance_le_expectation_sq hmem.aestronglyMeasurable).trans
      (canonical_martingale_second_moment_le_time K μ z T)
  have hc := meas_ge_le_variance_div_sq hmem hε
  have hmean := integral_partialSum_zero K μ z T
  calc
    P {w : ℕ → Y | ε ≤ |partialSum K z T w|} =
      P {w : ℕ → Y | ε ≤
        |partialSum K z T w - P[partialSum K z T]|} := by
          simp only [hmean, sub_zero]
    _ ≤ ENNReal.ofReal (variance (partialSum K z T) P / ε ^ 2) := hc
    _ ≤ ENNReal.ofReal ((T : ℝ) / ε ^ 2) :=
      ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right hvar (sq_nonneg ε))

end FiniteMarkovMartingaleTail
end MultipleLimit
end PermanssonResearch
