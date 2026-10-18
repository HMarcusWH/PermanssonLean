import PermanssonResearch.Probability.BoundedSquareStrongLaw
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.L2Space

/-! Bounded real innovations with zero conditional mean. Orthogonality and
the variance bound are proved under the actual supplied measure; they are
not independence assumptions. This supports general-state Markov tests. -/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal

namespace PermanssonResearch.Probability.BoundedInnovations

set_option autoImplicit false
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω))

structure Process where
  value : ℕ → Ω → ℝ
  measurable_next : ∀ t, Measurable[ℱ (t+1)] (value t)
  bounded : ∀ t ω, |value t ω| ≤ 1
  centered : ∀ t, μ[value t | ℱ t] =ᵐ[μ] (fun _ => (0 : ℝ))

namespace Process
variable {μ ℱ} (p : Process μ ℱ)

def total (T : ℕ) (ω : Ω) : ℝ := ∑ t ∈ Finset.range T, p.value t ω

theorem total_zero (ω : Ω) : p.total 0 ω = 0 := by simp [total]

theorem total_succ (T : ℕ) (ω : Ω) :
    p.total (T+1) ω = p.total T ω + p.value T ω := by simp [total,Finset.sum_range_succ]

theorem measurable_total (T : ℕ) : Measurable[ℱ T] (p.total T) := by
  unfold total
  apply Finset.measurable_fun_sum
  intro t ht
  exact (p.measurable_next t).mono
    (ℱ.mono (Finset.mem_range.mp ht)) le_rfl

theorem time_lipschitz (ω : Ω) (s t : ℕ) (hst : s ≤ t) :
    |p.total t ω - p.total s ω| ≤ ((t-s : ℕ) : ℝ) := by
  have he : p.total t ω - p.total s ω = ∑ i ∈ Finset.Ico s t, p.value i ω := by
    simpa only [total,Finset.sum_Ico_eq_sub _ hst]
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.Ico s t, |p.value i ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Ico s t, (1 : ℝ) := Finset.sum_le_sum (fun i _ => p.bounded i ω)
    _ = _ := by simp

theorem total_bound (T : ℕ) (ω : Ω) : |p.total T ω| ≤ (T : ℝ) := by
  simpa [total_zero] using p.time_lipschitz ω 0 T (Nat.zero_le T)

theorem integrable_value (t : ℕ) : Integrable (p.value t) μ := by
  apply Integrable.of_bound ((p.measurable_next t).mono (ℱ.le (t+1)) le_rfl).aestronglyMeasurable 1
  exact ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using p.bounded t ω)

theorem integrable_total (T : ℕ) : Integrable (p.total T) μ := by
  unfold total
  exact integrable_finset_sum _ (fun t _ => p.integrable_value t)

theorem value_square_bound (t : ℕ) (ω : Ω) : (p.value t ω)^2 ≤ 1 := by
  have h := abs_le.mp (p.bounded t ω)
  nlinarith [mul_nonneg (show 0 ≤ 1-p.value t ω by linarith)
    (show 0 ≤ 1+p.value t ω by linarith)]

theorem integrable_value_square (t : ℕ) : Integrable (fun ω => (p.value t ω)^2) μ := by
  have hm := ((p.measurable_next t).mono (ℱ.le (t+1)) le_rfl).pow_const 2
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact p.value_square_bound t ω)

theorem integral_value_square_le (t : ℕ) : (∫ ω, (p.value t ω)^2 ∂μ) ≤ 1 := by
  calc
    _ ≤ ∫ _ω : Ω, (1 : ℝ) ∂μ := integral_mono
      (p.integrable_value_square t) (integrable_const _) (p.value_square_bound t)
    _ = _ := by simp

theorem integrable_total_square (T : ℕ) : Integrable (fun ω => (p.total T ω)^2) μ := by
  have hm := ((p.measurable_total T).mono (ℱ.le T) le_rfl).pow_const 2
  apply Integrable.of_bound hm.aestronglyMeasurable ((T : ℝ)^2)
  exact ae_of_all _ (fun ω => by
    have hb := p.total_bound T ω
    have hprod : 0 ≤ ((T : ℝ)-|p.total T ω|) * (|p.total T ω|+(T : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hb) (add_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    have hs : |p.total T ω|^2 ≤ (T : ℝ)^2 := by nlinarith
    simpa only [Real.norm_eq_abs,abs_pow] using hs)

theorem integrable_total_mul_value (T : ℕ) :
    Integrable (fun ω => p.total T ω * p.value T ω) μ := by
  have hmM := (p.measurable_total T).mono (ℱ.le T) le_rfl
  have hmD := (p.measurable_next T).mono (ℱ.le (T+1)) le_rfl
  apply Integrable.of_bound (hmM.mul hmD).aestronglyMeasurable (T : ℝ)
  exact ae_of_all _ (fun ω => by
    simp only [Real.norm_eq_abs,Pi.mul_apply,abs_mul]
    exact (mul_le_mul_of_nonneg_left (p.bounded T ω) (abs_nonneg _)).trans
      (by simpa using p.total_bound T ω))

/-- Conditional centering cancels the actual covariance with every bounded
past-measurable observable. -/
theorem bounded_past_cross_zero (t : ℕ) (f : Ω → ℝ)
    (hf : StronglyMeasurable[ℱ t] f) (C : ℝ) (hb : ∀ ω, ‖f ω‖ ≤ C) :
    (∫ ω, f ω * p.value t ω ∂μ) = 0 := by
  have hpull : μ[f * p.value t | ℱ t] =ᵐ[μ] f * μ[p.value t | ℱ t] :=
    condExp_stronglyMeasurable_mul_of_bound (ℱ.le t) hf (p.integrable_value t) C (ae_of_all _ hb)
  have hz : μ[f * p.value t | ℱ t] =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    filter_upwards [hpull,p.centered t] with ω hω hc
    change (μ[f * p.value t | ℱ t]) ω = 0
    rw [hω]
    change f ω * (μ[p.value t | ℱ t]) ω = 0
    rw [hc,mul_zero]
  calc
    _ = ∫ ω, (μ[f * p.value t | ℱ t]) ω ∂μ := (integral_condExp (ℱ.le t)).symm
    _ = 0 := by rw [integral_congr_ae hz]; simp

theorem total_next_cross_zero (t : ℕ) :
    (∫ ω, p.total t ω * p.value t ω ∂μ) = 0 := by
  apply p.bounded_past_cross_zero t (p.total t) (p.measurable_total t).stronglyMeasurable (t : ℝ)
  intro ω
  simpa only [Real.norm_eq_abs] using p.total_bound t ω

/-- Linear second-moment growth, obtained from actual covariance
cancellation and bounded innovations. -/
theorem second_moment_le_time (T : ℕ) : (∫ ω, (p.total T ω)^2 ∂μ) ≤ (T : ℝ) := by
  induction T with
  | zero => simp [total_zero]
  | succ T ih =>
      have hSq := p.integrable_total_square T
      have hCross := p.integrable_total_mul_value T
      have hD := p.integrable_value_square T
      have he : (fun ω => (p.total (T+1) ω)^2) =
          (fun ω => (p.total T ω)^2 + 2*(p.total T ω*p.value T ω) + (p.value T ω)^2) := by
        funext ω
        rw [p.total_succ]
        ring
      rw [he]
      have hs1 : (∫ ω, (p.total T ω)^2 + 2*(p.total T ω*p.value T ω) + (p.value T ω)^2 ∂μ) =
          (∫ ω, (p.total T ω)^2 + 2*(p.total T ω*p.value T ω) ∂μ) +
            (∫ ω, (p.value T ω)^2 ∂μ) := by
        convert integral_add (hSq.add (hCross.const_mul 2)) hD using 1 <;> rfl
      have hs2 : (∫ ω, (p.total T ω)^2 + 2*(p.total T ω*p.value T ω) ∂μ) =
          (∫ ω, (p.total T ω)^2 ∂μ) + (∫ ω, 2*(p.total T ω*p.value T ω) ∂μ) := by
        convert integral_add hSq (hCross.const_mul 2) using 1 <;> rfl
      rw [hs1,hs2,integral_const_mul,p.total_next_cross_zero]
      have hle := add_le_add ih (p.integral_value_square_le T)
      simpa only [mul_zero,add_zero,Nat.cast_add,Nat.cast_one] using hle

theorem integral_value_zero (t : ℕ) : (∫ ω, p.value t ω ∂μ) = 0 := by
  calc
    _ = ∫ ω, (μ[p.value t | ℱ t]) ω ∂μ := (integral_condExp (ℱ.le t)).symm
    _ = _ := by rw [integral_congr_ae (p.centered t)]; simp

theorem integral_total_zero (T : ℕ) : (∫ ω, p.total T ω ∂μ) = 0 := by
  induction T with
  | zero => simp [total_zero]
  | succ T ih =>
      have he : p.total (T+1) = (fun ω => p.total T ω + p.value T ω) := by
        funext ω; exact p.total_succ T ω
      rw [he]
      have hs : (∫ ω, p.total T ω + p.value T ω ∂μ) =
          (∫ ω, p.total T ω ∂μ) + (∫ ω, p.value T ω ∂μ) := by
        convert integral_add (p.integrable_total T) (p.integrable_value T) using 1 <;> rfl
      rw [hs]
      simp only [ih,p.integral_value_zero,add_zero]

theorem total_memLp_two (T : ℕ) : MemLp (p.total T) 2 μ :=
  (memLp_two_iff_integrable_sq
    ((p.measurable_total T).mono (ℱ.le T) le_rfl).aestronglyMeasurable).2
    (p.integrable_total_square T)

theorem tail_le_time (T : ℕ) (ε : ℝ) (hε : 0 < ε) :
    μ {ω | ε ≤ |p.total T ω|} ≤ ENNReal.ofReal ((T : ℝ)/ε^2) := by
  have hmem := p.total_memLp_two T
  have hv : variance (p.total T) μ ≤ (T : ℝ) :=
    (variance_le_expectation_sq hmem.aestronglyMeasurable).trans (p.second_moment_le_time T)
  have hc := meas_ge_le_variance_div_sq hmem hε
  have hmean : μ[p.total T] = (0 : ℝ) := p.integral_total_zero T
  calc
    _ = μ {ω | ε ≤ |p.total T ω - μ[p.total T]|} := by rw [hmean]; simp only [sub_zero]
    _ ≤ ENNReal.ofReal (variance (p.total T) μ / ε^2) := hc
    _ ≤ _ := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hv (sq_nonneg ε))

theorem ae_strong_law :
    ∀ᵐ ω ∂μ, Tendsto (fun n => p.total (n+1) ω / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
  BoundedSquareStrongLaw.ae_strong_law μ p.total p.tail_le_time p.time_lipschitz

end Process
end
end PermanssonResearch.Probability.BoundedInnovations
