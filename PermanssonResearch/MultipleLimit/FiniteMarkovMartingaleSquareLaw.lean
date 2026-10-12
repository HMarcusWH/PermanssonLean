import PermanssonResearch.MultipleLimit.FiniteMarkovMartingaleTail
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic

/-!
# C53-04 — square-horizon martingale strong law on genuine Markov paths

The exact centered Markov martingale variance bound E[M_T²] ≤ T gives
summable deviation probabilities at the sparse horizons (n+1)².
Apply the FIRST Borel–Cantelli lemma without an independence assumption
to deduce normalized almost-sure convergence along these horizons.

A separate bounded-increment interpolation theorem must then connect
square-horizon convergence to ALL time horizons. Do not call this an
all-horizon martingale strong law until that second theorem is proved.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteMarkovMartingaleSquareLaw

open FiniteCanonicalPath
open FiniteMarkovMartingaleStep
open FiniteMarkovMartingaleTail

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [StandardBorelSpace Y]
variable [Nonempty Y] [DecidableEq Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- Start the sparse square horizons at one to keep normalization defined. -/
def squareHorizon (n : ℕ) : ℕ := (n+1)^2

theorem squareHorizon_pos (n : ℕ) : 0 < squareHorizon n := by
  simp [squareHorizon]

noncomputable def normalizedSquare (z : Y) (n : ℕ)
    (w : ℕ → Y) : ℝ :=
  partialSum K z (squareHorizon n) w / (squareHorizon n : ℝ)

/-- A genuine tail bound of O((n+1)^(-2)) along square horizons. -/
theorem square_event_probability_bound
    (μ : ProbabilityMeasure Y) (z : Y) (n : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    (canonicalPathLaw K μ.toMeasure)
      {w : ℕ → Y | ε ≤ |normalizedSquare K z n w|} ≤
        ENNReal.ofReal ((ε^2)⁻¹ * ((squareHorizon n : ℝ)⁻¹)) := by
  let P := canonicalPathLaw K μ.toMeasure
  have hs : (0 : ℝ) < (squareHorizon n : ℝ) :=
    Nat.cast_pos.mpr (squareHorizon_pos n)
  have hEvent :
      {w : ℕ → Y | ε ≤ |normalizedSquare K z n w|} =
        {w : ℕ → Y | ε * (squareHorizon n : ℝ) ≤
          |partialSum K z (squareHorizon n) w|} := by
    ext w
    simp only [Set.mem_setOf_eq, normalizedSquare, abs_div,
      abs_of_pos hs]
    exact le_div_iff₀ hs
  rw [hEvent]
  calc
    P {w : ℕ → Y | ε * (squareHorizon n : ℝ) ≤
        |partialSum K z (squareHorizon n) w|} ≤
      ENNReal.ofReal ((squareHorizon n : ℝ) /
        (ε * (squareHorizon n : ℝ)) ^ 2) :=
      partialSum_tail_le_time K μ z (squareHorizon n)
        (ε * (squareHorizon n : ℝ)) (mul_pos hε hs)
    _ = ENNReal.ofReal ((ε^2)⁻¹ * ((squareHorizon n : ℝ)⁻¹)) := by
      congr 1
      field_simp [ne_of_gt hε, ne_of_gt hs]
      ring

/-- The positive real square-horizon reciprocal series is summable. -/
theorem square_reciprocal_summable :
    Summable (fun n : ℕ => (squareHorizon n : ℝ)⁻¹) := by
  have h : Summable (fun n : ℕ => ((n : ℝ)^2)⁻¹) :=
    (summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  convert (summable_nat_add_iff 1).mpr h using 1
  ext n
  simp [squareHorizon]

/-- First Borel–Cantelli: deviations larger than a fixed positive
threshold only occur finitely often ALONG THE SQUARE HORIZONS. -/
theorem square_normalized_eventually_small
    (μ : ProbabilityMeasure Y) (z : Y)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∀ᶠ n in atTop, |normalizedSquare K z n w| < ε := by
  let P := canonicalPathLaw K μ.toMeasure
  have hseries :
      Summable (fun n : ℕ =>
        (ε^2)⁻¹ * ((squareHorizon n : ℝ)⁻¹)) :=
    (square_reciprocal_summable).mul_left ((ε^2)⁻¹)
  have hnonneg (n : ℕ) :
      0 ≤ (ε^2)⁻¹ * ((squareHorizon n : ℝ)⁻¹) := by
    positivity
  have hfinite :
      (∑' n : ℕ, ENNReal.ofReal
        ((ε^2)⁻¹ * ((squareHorizon n : ℝ)⁻¹))) ≠ ∞ := by
    have ht := ENNReal.ofReal_tsum_of_nonneg hnonneg hseries
    rw [← ht]
    exact ENNReal.ofReal_ne_top
  have hevents :
      (∑' n : ℕ, P {w : ℕ → Y |
          ε ≤ |normalizedSquare K z n w|}) ≠ ∞ := by
    apply ne_top_of_le_ne_top hfinite
    exact ENNReal.tsum_le_tsum (fun n =>
      square_event_probability_bound K μ z n ε hε)
  filter_upwards [ae_eventually_notMem hevents] with w hw
  simpa only [Set.mem_setOf_eq, not_le] using hw

/-- Borel–Cantelli at rational thresholds gives the exact zero
limit along squares, for arbitrary initial probability measures. -/
theorem square_normalized_ae_tendsto_zero
    (μ : ProbabilityMeasure Y) (z : Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n : ℕ => normalizedSquare K z n w)
        atTop (𝓝 (0 : ℝ)) := by
  have hcounts (k : ℕ) :
      ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
        ∀ᶠ n in atTop,
          |normalizedSquare K z n w| < (1 : ℝ) / (k+1) :=
    square_normalized_eventually_small K μ z ((1 : ℝ) / (k+1))
      (by positivity)
  filter_upwards [ae_all_iff.mpr hcounts] with w hw
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
  filter_upwards [hw k] with n hn
  simpa only [Real.dist_eq, sub_zero] using (lt_trans hn hk)

end FiniteMarkovMartingaleSquareLaw
end MultipleLimit
end PermanssonResearch
