import PermanssonResearch.MultipleLimit.FiniteMarkovMartingaleOrthogonality
import PermanssonResearch.MultipleLimit.FiniteMarkovMartingaleMoments
import Mathlib.Tactic

/-!
# C53-03 — actual canonical martingale second-moment growth

Use exact centered-increment orthogonality, true one-step canonical
second moments, and the pointwise bounded-increment sum to show that
E[M_T²] ≤ T for all finite horizons and every initial probability law.
No IID, stationarity or aperiodicity assumption is made.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteMarkovMartingaleVariance

open FiniteCanonicalPath
open FiniteMarkovMartingaleStep
open FiniteMarkovInterpolation
open FiniteMarkovMartingaleMoments
open FiniteMarkovMartingaleOrthogonality

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [StandardBorelSpace Y]
variable [Nonempty Y] [DecidableEq Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

theorem partialSum_abs_le_time (z : Y) (T : ℕ)
    (w : ℕ → Y) :
    |partialSum K z T w| ≤ (T : ℝ) := by
  have h := partialSum_time_lipschitz K z w
    (s := 0) (t := T) (Nat.zero_le T)
  simpa [partialSum_zero] using h

theorem partialSum_sq_integrable (μ : ProbabilityMeasure Y)
    (z : Y) (T : ℕ) :
    Integrable (fun w : ℕ → Y => (partialSum K z T w) ^ 2)
      (canonicalPathLaw K μ.toMeasure) := by
  have hm : Measurable (fun w : ℕ → Y => (partialSum K z T w) ^ 2) :=
    ((partialSum_measurable_at K z T).mono
      ((pastFiltration (Y := Y)).le T) le_rfl).pow_const 2
  apply Integrable.of_bound hm.aestronglyMeasurable ((T : ℝ) ^ 2)
  exact ae_of_all _ (fun w => by
    have hb := partialSum_abs_le_time K z T w
    have hn : 0 ≤ (T : ℝ) := Nat.cast_nonneg _
    have hprod : 0 ≤ ((T : ℝ) - |partialSum K z T w|) *
        (|partialSum K z T w| + (T : ℝ)) := by
      exact mul_nonneg (sub_nonneg.mpr hb)
        (add_nonneg (abs_nonneg (partialSum K z T w)) hn)
    have htwo : |partialSum K z T w| ^ 2 ≤ (T : ℝ) ^ 2 := by
      nlinarith
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs] using htwo)

theorem partialSum_mul_increment_integrable (μ : ProbabilityMeasure Y)
    (z : Y) (T : ℕ) :
    Integrable (fun w : ℕ → Y =>
      partialSum K z T w * increment K z T w)
      (canonicalPathLaw K μ.toMeasure) := by
  have hmM : Measurable (partialSum K z T) :=
    (partialSum_measurable_at K z T).mono
      ((pastFiltration (Y := Y)).le T) le_rfl
  have hmD : Measurable (increment K z T) :=
    (increment_measurable_at K z T).mono
      ((pastFiltration (Y := Y)).le (T+1)) le_rfl
  apply Integrable.of_bound (hmM.mul hmD).aestronglyMeasurable (T : ℝ)
  exact ae_of_all _ (fun w => by
    have hbM := partialSum_abs_le_time K z T w
    have hbD := increment_bounded K z T w
    simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    calc
      |partialSum K z T w| * |increment K z T w| ≤
        |partialSum K z T w| * 1 :=
          mul_le_mul_of_nonneg_left hbD (abs_nonneg _)
      _ = |partialSum K z T w| := by ring
      _ ≤ (T : ℝ) := hbM)

/-- The central growth bound under the ACTUAL infinite Markov path
measure. Martingale independence is nowhere assumed. -/
theorem canonical_martingale_second_moment_le_time
    (μ : ProbabilityMeasure Y) (z : Y) (T : ℕ) :
    (∫ w, (partialSum K z T w) ^ 2
      ∂canonicalPathLaw K μ.toMeasure) ≤ (T : ℝ) := by
  let P := canonicalPathLaw K μ.toMeasure
  induction T with
  | zero =>
      simp [partialSum_zero]
  | succ T ih =>
      have hSq := partialSum_sq_integrable K μ z T
      have hCross := partialSum_mul_increment_integrable K μ z T
      have hD := increment_sq_integrable K μ z T
      have hCov := partialSum_next_increment_orthogonal K μ z T
      have hDle := integral_increment_sq_le_one K μ z T
      have hpoint (w : ℕ → Y) :
          (partialSum K z (T+1) w) ^ 2 =
            (partialSum K z T w) ^ 2 +
              2 * (partialSum K z T w * increment K z T w) +
                (increment K z T w) ^ 2 := by
        rw [partialSum_succ]
        ring
      calc
        (∫ w, (partialSum K z (T+1) w) ^ 2 ∂P) =
          ∫ w, (partialSum K z T w) ^ 2 +
            2 * (partialSum K z T w * increment K z T w) +
              (increment K z T w) ^ 2 ∂P := by
                exact integral_congr_ae (ae_of_all P hpoint)
        _ = (∫ w, (partialSum K z T w) ^ 2 ∂P) +
            2 * (∫ w, partialSum K z T w *
              increment K z T w ∂P) +
              (∫ w, (increment K z T w) ^ 2 ∂P) := by
                change (∫ w,
                  (((fun w : ℕ → Y => (partialSum K z T w) ^ 2) +
                    (fun w : ℕ → Y =>
                      2 * (partialSum K z T w * increment K z T w))) +
                    (fun w : ℕ → Y => (increment K z T w) ^ 2)) w ∂P) = _
                rw [integral_add (hSq.add (hCross.const_mul 2)) hD,
                  integral_add hSq (hCross.const_mul 2),
                  integral_const_mul]
        _ = (∫ w, (partialSum K z T w) ^ 2 ∂P) +
            (∫ w, (increment K z T w) ^ 2 ∂P) := by
              rw [hCov]
              ring
        _ ≤ (T : ℝ) + 1 := add_le_add ih hDle
        _ = ((T+1 : ℕ) : ℝ) := by norm_num

end FiniteMarkovMartingaleVariance
end MultipleLimit
end PermanssonResearch
