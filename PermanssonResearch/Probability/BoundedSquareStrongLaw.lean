import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! A general square-subsequence strong law with bounded interpolation.
The finite-horizon tail bound and the pathwise time-Lipschitz estimate are
explicit inputs. No independence, stationary initial law, or finite state
space is assumed. A separate canonical-Markov module discharges these inputs
for bounded continuous Markov innovations. -/

open Filter MeasureTheory
open scoped Topology ENNReal

namespace PermanssonResearch.Probability.BoundedSquareStrongLaw

set_option autoImplicit false
noncomputable section

def squareHorizon (n : ℕ) : ℕ := (n+1)^2

theorem squareHorizon_pos (n : ℕ) : 0 < squareHorizon n := by simp [squareHorizon]

theorem square_reciprocal_summable :
    Summable (fun n : ℕ => (squareHorizon n : ℝ)⁻¹) := by
  have h : Summable (fun n : ℕ => ((n : ℝ)^2)⁻¹) :=
    (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  convert (summable_nat_add_iff 1).mpr h using 1
  ext n
  simp [squareHorizon]

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) (M : ℕ → Ω → ℝ)

def normalizedSquare (n : ℕ) (ω : Ω) : ℝ :=
  M (squareHorizon n) ω / (squareHorizon n : ℝ)

theorem square_event_probability_bound
    (htail : ∀ (T : ℕ) (ε : ℝ), 0 < ε →
      μ {ω | ε ≤ |M T ω|} ≤ ENNReal.ofReal ((T : ℝ) / ε^2))
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    μ {ω | ε ≤ |normalizedSquare M n ω|} ≤
      ENNReal.ofReal ((ε^2)⁻¹ * (squareHorizon n : ℝ)⁻¹) := by
  have hs : (0 : ℝ) < (squareHorizon n : ℝ) :=
    Nat.cast_pos.mpr (squareHorizon_pos n)
  have he : {ω | ε ≤ |normalizedSquare M n ω|} =
      {ω | ε * (squareHorizon n : ℝ) ≤ |M (squareHorizon n) ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq, normalizedSquare, abs_div, abs_of_pos hs]
    exact le_div_iff₀ hs
  rw [he]
  calc
    _ ≤ ENNReal.ofReal ((squareHorizon n : ℝ) / (ε * (squareHorizon n : ℝ))^2) :=
      htail _ _ (mul_pos hε hs)
    _ = _ := by
      congr 1
      field_simp [ne_of_gt hε,ne_of_gt hs]
      <;> ring

theorem square_eventually_small
    (htail : ∀ (T : ℕ) (ε : ℝ), 0 < ε →
      μ {ω | ε ≤ |M T ω|} ≤ ENNReal.ofReal ((T : ℝ) / ε^2))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, |normalizedSquare M n ω| < ε := by
  have hs : Summable (fun n : ℕ => (ε^2)⁻¹ * (squareHorizon n : ℝ)⁻¹) :=
    square_reciprocal_summable.mul_left _
  have hn (n : ℕ) : 0 ≤ (ε^2)⁻¹ * (squareHorizon n : ℝ)⁻¹ := by positivity
  have hf : (∑' n : ℕ, ENNReal.ofReal ((ε^2)⁻¹ * (squareHorizon n : ℝ)⁻¹)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hn hs]
    exact ENNReal.ofReal_ne_top
  have he : (∑' n : ℕ, μ {ω | ε ≤ |normalizedSquare M n ω|}) ≠ ∞ := by
    apply ne_top_of_le_ne_top hf
    exact ENNReal.tsum_le_tsum (fun n => square_event_probability_bound μ M htail n ε hε)
  filter_upwards [ae_eventually_notMem he] with ω hω
  simpa only [Set.mem_setOf_eq,not_le] using hω

theorem square_ae_tendsto_zero
    (htail : ∀ (T : ℕ) (ε : ℝ), 0 < ε →
      μ {ω | ε ≤ |M T ω|} ≤ ENNReal.ofReal ((T : ℝ) / ε^2)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => normalizedSquare M n ω) atTop (𝓝 0) := by
  have hc (k : ℕ) : ∀ᵐ ω ∂μ,
      ∀ᶠ n in atTop, |normalizedSquare M n ω| < (1 : ℝ) / (k+1) :=
    square_eventually_small μ M htail _ (by positivity)
  filter_upwards [ae_all_iff.mpr hc] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hω k)
  refine ⟨N,fun n hn => ?_⟩
  simpa only [Real.dist_eq,sub_zero] using (hN n hn).trans hk

private theorem sqrt_succ_tendsto_atTop :
    Tendsto (fun n : ℕ => Nat.sqrt (n+1)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (k^2)] with n hn
  exact (Nat.le_sqrt').mpr (by omega)

private theorem sqrt_pred_tendsto_atTop :
    Tendsto (fun n : ℕ => Nat.sqrt (n+1)-1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [sqrt_succ_tendsto_atTop.eventually (eventually_ge_atTop (k+1))] with n hn
  omega

private theorem squareHorizon_sqrt_pred (n : ℕ) :
    squareHorizon (Nat.sqrt (n+1)-1) = (Nat.sqrt (n+1))^2 := by
  have hk : 1 ≤ Nat.sqrt (n+1) := (Nat.le_sqrt').mpr (by omega)
  simp [squareHorizon,Nat.sub_add_cancel hk]

def relativeSquareGap (n : ℕ) : ℝ :=
  (((n+1 : ℕ) : ℝ) - (Nat.sqrt (n+1) : ℝ)^2) / ((n+1 : ℕ) : ℝ)

private theorem relativeSquareGap_nonneg (n : ℕ) : 0 ≤ relativeSquareGap n := by
  have hle : (Nat.sqrt (n+1) : ℝ)^2 ≤ ((n+1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sqrt_le' (n+1)
  exact div_nonneg (sub_nonneg.mpr hle) (by positivity)

private theorem relativeSquareGap_le_inverse_root (n : ℕ) :
    relativeSquareGap n ≤ 2 * (Nat.sqrt (n+1) : ℝ)⁻¹ + ((Nat.sqrt (n+1) : ℝ)⁻¹)^2 := by
  let T := n+1
  let k := Nat.sqrt T
  have hkN : 0 < k := by dsimp [k,T]; exact Nat.sqrt_pos.mpr (Nat.succ_pos n)
  have hk : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hkN
  have hT : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr (by dsimp [T]; omega)
  have hloN : k^2 ≤ T := Nat.sqrt_le' T
  have hhiN : T < (k+1)^2 := by
    dsimp [k]
    simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' T
  have hlo : (k : ℝ)^2 ≤ (T : ℝ) := by exact_mod_cast hloN
  have hhi : (T : ℝ) < ((k : ℝ)+1)^2 := by exact_mod_cast hhiN
  have hg : (T : ℝ) - (k : ℝ)^2 ≤ 2 * (k : ℝ) + 1 := by nlinarith
  have hr : ((T : ℝ) - (k : ℝ)^2) / (T : ℝ) ≤
      (2 * (k : ℝ)+1) / (k : ℝ)^2 := by
    apply (div_le_div_iff₀ hT (sq_pos_of_pos hk)).mpr
    calc
      _ ≤ (2 * (k : ℝ)+1) * (k : ℝ)^2 := mul_le_mul_of_nonneg_right hg (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
  have he : (2 * (k : ℝ)+1) / (k : ℝ)^2 = 2 * (k : ℝ)⁻¹ + ((k : ℝ)⁻¹)^2 := by
    field_simp [ne_of_gt hk]
  exact hr.trans_eq he

theorem relativeSquareGap_tendsto_zero : Tendsto relativeSquareGap atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (Nat.sqrt (n+1) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp sqrt_succ_tendsto_atTop)
  have hr : Tendsto (fun n : ℕ => 2 * (Nat.sqrt (n+1) : ℝ)⁻¹ +
      ((Nat.sqrt (n+1) : ℝ)⁻¹)^2) atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul hi).add (hi.pow 2) using 1 <;> simp
  exact squeeze_zero relativeSquareGap_nonneg relativeSquareGap_le_inverse_root hr

theorem normalized_le_square_and_gap
    (hL : ∀ (ω : Ω) (s t : ℕ), s ≤ t → |M t ω - M s ω| ≤ ((t-s : ℕ) : ℝ))
    (ω : Ω) (n : ℕ) :
    |M (n+1) ω / ((n+1 : ℕ) : ℝ)| ≤
      |normalizedSquare M (Nat.sqrt (n+1)-1) ω| + relativeSquareGap n := by
  let T := n+1
  let k := Nat.sqrt T
  let s := k^2
  have hT : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr (by dsimp [T]; omega)
  have hk : (0 : ℝ) < (k : ℝ) := by
    apply Nat.cast_pos.mpr
    dsimp [k,T]
    exact Nat.sqrt_pos.mpr (Nat.succ_pos n)
  have hs : (0 : ℝ) < (s : ℝ) := by dsimp [s]; positivity
  have hsT : s ≤ T := Nat.sqrt_le' T
  have hst : (s : ℝ) ≤ (T : ℝ) := Nat.cast_le.mpr hsT
  have hr0 : 0 ≤ (s : ℝ) / (T : ℝ) := div_nonneg (by positivity) hT.le
  have hr1 : (s : ℝ) / (T : ℝ) ≤ 1 := (div_le_one hT).mpr hst
  have he : M T ω / (T : ℝ) = (M s ω / (s : ℝ)) * ((s : ℝ)/(T : ℝ)) +
      (M T ω - M s ω) / (T : ℝ) := by
    field_simp [ne_of_gt hs,ne_of_gt hT]
    ring
  have hfirst : |(M s ω / (s : ℝ)) * ((s : ℝ)/(T : ℝ))| ≤ |M s ω / (s : ℝ)| := by
    rw [abs_mul,abs_of_nonneg hr0]
    exact (mul_le_mul_of_nonneg_left hr1 (abs_nonneg _)).trans_eq (mul_one _)
  have hsecond : |(M T ω - M s ω) / (T : ℝ)| ≤ ((T : ℝ)-(s : ℝ))/(T : ℝ) := by
    rw [abs_div,abs_of_pos hT]
    exact div_le_div_of_nonneg_right ((hL ω s T hsT).trans_eq (Nat.cast_sub hsT)) hT.le
  have hb : |M T ω / (T : ℝ)| ≤ |M s ω / (s : ℝ)| + ((T : ℝ)-(s : ℝ))/(T : ℝ) := by
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  simpa only [normalizedSquare,squareHorizon_sqrt_pred n,relativeSquareGap,T,k,s,Nat.cast_pow] using hb

theorem full_tendsto_of_square
    (hL : ∀ (ω : Ω) (s t : ℕ), s ≤ t → |M t ω - M s ω| ≤ ((t-s : ℕ) : ℝ))
    (ω : Ω) (hs : Tendsto (fun n => normalizedSquare M n ω) atTop (𝓝 0)) :
    Tendsto (fun n => M (n+1) ω / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hsel := hs.comp sqrt_pred_tendsto_atTop
  have hu : Tendsto (fun n => |normalizedSquare M (Nat.sqrt (n+1)-1) ω| +
      relativeSquareGap n) atTop (𝓝 0) := by
    simpa using hsel.abs.add relativeSquareGap_tendsto_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero (fun n => abs_nonneg _)
    (normalized_le_square_and_gap M hL ω) hu

/-- The all-horizon strong law derived from a genuine second-moment tail
estimate and bounded increments, on the very same probability space. -/
theorem ae_strong_law
    (htail : ∀ (T : ℕ) (ε : ℝ), 0 < ε →
      μ {ω | ε ≤ |M T ω|} ≤ ENNReal.ofReal ((T : ℝ) / ε^2))
    (hL : ∀ (ω : Ω) (s t : ℕ), s ≤ t → |M t ω - M s ω| ≤ ((t-s : ℕ) : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => M (n+1) ω / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  filter_upwards [square_ae_tendsto_zero μ M htail] with ω hω
  exact full_tendsto_of_square M hL ω hω

end
end PermanssonResearch.Probability.BoundedSquareStrongLaw
