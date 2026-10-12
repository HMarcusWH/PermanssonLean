import PermanssonResearch.MultipleLimit.FiniteMarkovMartingaleSquareLaw
import PermanssonResearch.MultipleLimit.FiniteMarkovInterpolation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# C53-04 — unconditional finite Markov innovation strong law

The previous square-horizon theorem provides a genuine almost-sure
subsequence limit under the canonical infinite Markov path law.
The bounded-increment inequality closes the gaps between successive
squares. This module is intended to prove an ALL-HORIZONS martingale
strong law for every finite stochastic kernel and arbitrary starting law,
without stationarity, irreducibility or aperiodicity assumptions.

No occupation limit is assumed here: the result is a probability-theoretic
input to the subsequent finite empirical stationarity bridge.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteMarkovMartingaleSLLN

open FiniteCanonicalPath
open FiniteMarkovMartingaleStep
open FiniteMarkovMartingaleSquareLaw
open FiniteMarkovInterpolation

/-- The integer square root of positive time tends to infinity. -/
private theorem sqrt_succ_tendsto_atTop :
    Tendsto (fun n : ℕ => Nat.sqrt (n+1)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (k^2)] with n hn
  exact (Nat.le_sqrt').mpr (by omega)

/-- The previous sparse-square index tends to infinity as well. -/
private theorem sqrt_pred_tendsto_atTop :
    Tendsto (fun n : ℕ => Nat.sqrt (n+1)-1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [sqrt_succ_tendsto_atTop.eventually
    (eventually_ge_atTop (k+1))] with n hn
  omega

/-- The selected previous square is exactly the square-horizon scheme
used by the Borel–Cantelli theorem (including at time one). -/
private theorem squareHorizon_sqrt_pred (n : ℕ) :
    squareHorizon (Nat.sqrt (n+1)-1) = (Nat.sqrt (n+1))^2 := by
  have hk : 1 ≤ Nat.sqrt (n+1) :=
    (Nat.le_sqrt').mpr (by omega)
  simp [squareHorizon, Nat.sub_add_cancel hk]

noncomputable def relativeSquareGap (n : ℕ) : ℝ :=
  (((n+1 : ℕ) : ℝ) - ((Nat.sqrt (n+1) : ℝ)^2)) / ((n+1 : ℕ) : ℝ)

private theorem relativeSquareGap_nonneg (n : ℕ) :
    0 ≤ relativeSquareGap n := by
  have hle : (Nat.sqrt (n+1) : ℝ)^2 ≤ ((n+1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sqrt_le' (n+1))
  exact div_nonneg (sub_nonneg.mpr hle) (by positivity)

/-- The relative gap between time T and its previous square is O(1/√T),
expressed as a concrete rational inequality valid even for T=1. -/
private theorem relativeSquareGap_le_inverse_root (n : ℕ) :
    relativeSquareGap n ≤
      2 * ((Nat.sqrt (n+1) : ℝ)⁻¹) +
      ((Nat.sqrt (n+1) : ℝ)⁻¹)^2 := by
  let T : ℕ := n+1
  let k : ℕ := Nat.sqrt T
  have hkNat : 0 < k := by
    dsimp [k, T]
    exact (Nat.sqrt_pos).mpr (Nat.succ_pos n)
  have hk : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hkNat
  have hT : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr (by dsimp [T]; omega)
  have hloNat : k^2 ≤ T := by
    dsimp [k]
    exact Nat.sqrt_le' T
  have hhiNat : T < (k+1)^2 := by
    dsimp [k]
    simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' T
  have hlo : (k : ℝ)^2 ≤ (T : ℝ) := by exact_mod_cast hloNat
  have hhi : (T : ℝ) < ((k : ℝ)+1)^2 := by exact_mod_cast hhiNat
  have hgap : (T : ℝ) - (k : ℝ)^2 ≤ 2 * (k : ℝ) + 1 := by
    nlinarith
  have hr : ((T : ℝ) - (k : ℝ)^2) / (T : ℝ) ≤
      (2 * (k : ℝ) + 1) / (k : ℝ)^2 := by
    apply (div_le_div_iff₀ hT (sq_pos_of_pos hk)).mpr
    calc
      ((T : ℝ) - (k : ℝ)^2) * (k : ℝ)^2 ≤
          (2 * (k : ℝ) + 1) * (k : ℝ)^2 :=
        mul_le_mul_of_nonneg_right hgap (sq_nonneg _)
      _ ≤ (2 * (k : ℝ) + 1) * (T : ℝ) :=
        mul_le_mul_of_nonneg_left hlo (by positivity)
  have hfield : (2 * (k : ℝ) + 1) / (k : ℝ)^2 =
      2 * ((k : ℝ)⁻¹) + ((k : ℝ)⁻¹)^2 := by
    field_simp [ne_of_gt hk]
    ring
  change ((T : ℝ) - (k : ℝ)^2) / (T : ℝ) ≤
      2 * ((k : ℝ)⁻¹) + ((k : ℝ)⁻¹)^2
  exact hr.trans_eq hfield

/-- The relative gap genuinely vanishes along the full time sequence. -/
private theorem relativeSquareGap_tendsto_zero :
    Tendsto relativeSquareGap atTop (𝓝 (0 : ℝ)) := by
  have hinv : Tendsto
      (fun n : ℕ => ((Nat.sqrt (n+1) : ℝ)⁻¹))
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp sqrt_succ_tendsto_atTop)
  have hright : Tendsto
      (fun n : ℕ =>
        2 * ((Nat.sqrt (n+1) : ℝ)⁻¹) +
          ((Nat.sqrt (n+1) : ℝ)⁻¹)^2)
      atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds.mul hinv).add (hinv.pow 2) using 1 <;> simp
  exact squeeze_zero relativeSquareGap_nonneg
    relativeSquareGap_le_inverse_root hright

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [StandardBorelSpace Y]
variable [Nonempty Y] [DecidableEq Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- At each full time horizon the normalized martingale is bounded by
its normalized value at the previous square plus the relative time gap.
No probability arguments enter this deterministic interpolation lemma. -/
theorem partialSum_normalized_le_square_and_gap
    (z : Y) (w : ℕ → Y) (n : ℕ) :
    |partialSum K z (n+1) w / (((n+1 : ℕ) : ℝ))| ≤
      |normalizedSquare K z (Nat.sqrt (n+1)-1) w| +
        relativeSquareGap n := by
  let T : ℕ := n+1
  let k : ℕ := Nat.sqrt T
  let s : ℕ := k^2
  have hT : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr (by dsimp [T]; omega)
  have hk : (0 : ℝ) < (k : ℝ) := by
    apply Nat.cast_pos.mpr
    dsimp [k, T]
    exact (Nat.sqrt_pos).mpr (Nat.succ_pos n)
  have hs : (0 : ℝ) < (s : ℝ) := by
    dsimp [s]
    positivity
  have hsT : s ≤ T := by
    dsimp [s, k]
    exact Nat.sqrt_le' T
  have hst : (s : ℝ) ≤ (T : ℝ) := Nat.cast_le.mpr hsT
  have hratio0 : 0 ≤ (s : ℝ) / (T : ℝ) := div_nonneg (by positivity) hT.le
  have hratio1 : (s : ℝ) / (T : ℝ) ≤ 1 :=
    (div_le_one hT).mpr hst
  have hsplit :
      partialSum K z T w / (T : ℝ) =
        (partialSum K z s w / (s : ℝ)) * ((s : ℝ)/(T : ℝ)) +
          (partialSum K z T w - partialSum K z s w) / (T : ℝ) := by
    field_simp [ne_of_gt hs, ne_of_gt hT]
    ring
  have hfirst :
      |(partialSum K z s w / (s : ℝ)) * ((s : ℝ)/(T : ℝ))| ≤
        |partialSum K z s w / (s : ℝ)| := by
    rw [abs_mul, abs_of_nonneg hratio0]
    calc
      |partialSum K z s w / (s : ℝ)| * ((s : ℝ)/(T : ℝ)) ≤
          |partialSum K z s w / (s : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left hratio1 (abs_nonneg _)
      _ = |partialSum K z s w / (s : ℝ)| := mul_one _
  have hsecond :
      |(partialSum K z T w - partialSum K z s w) / (T : ℝ)| ≤
        ((T : ℝ) - (s : ℝ)) / (T : ℝ) := by
    rw [abs_div, abs_of_pos hT]
    have hL := partialSum_time_lipschitz K z w
      (s := s) (t := T) hsT
    have hcast : (((T-s : ℕ) : ℝ)) = (T : ℝ) - (s : ℝ) :=
      Nat.cast_sub hsT
    exact (div_le_div_of_nonneg_right
      (hL.trans_eq hcast) hT.le)
  have hbound :
      |partialSum K z T w / (T : ℝ)| ≤
        |partialSum K z s w / (s : ℝ)| +
          ((T : ℝ) - (s : ℝ)) / (T : ℝ) := by
    rw [hsplit]
    calc
      |(partialSum K z s w / (s : ℝ)) * ((s : ℝ)/(T : ℝ)) +
        (partialSum K z T w - partialSum K z s w)/(T : ℝ)| ≤
          |(partialSum K z s w / (s : ℝ)) * ((s : ℝ)/(T : ℝ))| +
            |(partialSum K z T w - partialSum K z s w)/(T : ℝ)| :=
        abs_add_le _ _
      _ ≤ |partialSum K z s w / (s : ℝ)| +
          ((T : ℝ) - (s : ℝ)) / (T : ℝ) :=
        add_le_add hfirst hsecond
  simpa only [normalizedSquare, squareHorizon_sqrt_pred n,
    relativeSquareGap, T, k, s, Nat.cast_pow] using hbound

/-- Sparse-square convergence, bounded increments and vanishing
relative square gaps imply the genuine all-horizon strong law. -/
theorem partialSum_full_tendsto_of_square
    (z : Y) (w : ℕ → Y)
    (hSquare : Tendsto (fun n : ℕ => normalizedSquare K z n w)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n : ℕ =>
      partialSum K z (n+1) w / (((n+1 : ℕ) : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
  have hselect :
      Tendsto (fun n : ℕ =>
        normalizedSquare K z (Nat.sqrt (n+1)-1) w)
        atTop (𝓝 (0 : ℝ)) :=
    hSquare.comp sqrt_pred_tendsto_atTop
  have hUpper : Tendsto (fun n : ℕ =>
      |normalizedSquare K z (Nat.sqrt (n+1)-1) w| +
        relativeSquareGap n)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hselect.abs.add relativeSquareGap_tendsto_zero
  have hAbs : Tendsto (fun n : ℕ =>
      |partialSum K z (n+1) w / (((n+1 : ℕ) : ℝ))|)
      atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun n => abs_nonneg _)
      (partialSum_normalized_le_square_and_gap K z w) hUpper
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using hAbs

/-- Unconditional, periodicity-safe, canonical martingale strong law.
It holds for EVERY finite stochastic chain and starting probability law. -/
theorem canonical_partialSum_strong_law
    (μ : ProbabilityMeasure Y) (z : Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n : ℕ =>
        partialSum K z (n+1) w / (((n+1 : ℕ) : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
  filter_upwards [square_normalized_ae_tendsto_zero K μ z] with w hw
  exact partialSum_full_tendsto_of_square K z w hw

/-- The all-state finite conjunction uses actual a.e. intersections,
not a chosen typical trajectory or an independent path measure. -/
theorem canonical_partialSum_strong_law_all_states
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∀ z : Y,
        Tendsto (fun n : ℕ =>
          partialSum K z (n+1) w / (((n+1 : ℕ) : ℝ)))
          atTop (𝓝 (0 : ℝ)) := by
  rw [ae_all_iff]
  exact fun z => canonical_partialSum_strong_law K μ z

end FiniteMarkovMartingaleSLLN
end MultipleLimit
end PermanssonResearch
