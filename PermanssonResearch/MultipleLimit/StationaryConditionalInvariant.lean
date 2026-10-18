import PermanssonResearch.MultipleLimit.StationaryConditionalLaw
import PermanssonResearch.MultipleLimit.CanonicalBoundedInnovations
import PermanssonResearch.Probability.StandardBorelKernelEquality
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Invariance of the conditional random probability on an arbitrary standard
Borel state space. This has its own proof: stationary Birkhoff averages for
f and Kf, the actual bounded Markov innovation strong law, and the countable
determining-set whole-kernel equality theorem. No Feller or compactness
assumption is used or silently imported into the statement. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace PermanssonResearch.MultipleLimit.StationaryConditionalInvariant

set_option autoImplicit false
noncomputable section
variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
open FiniteCanonicalPath StationaryConditional CanonicalBoundedInnovations
open PermanssonResearch.Probability

def average (f : Y → ℝ) (n : ℕ) (w : ℕ → Y) : ℝ :=
  (∑ t ∈ Finset.range (n+1),f (w t))/((n+1:ℕ):ℝ)

theorem endpoint_tendsto (f : Y → ℝ) (B : ℝ) (hb : ∀ y, |f y| ≤ B) (w : ℕ → Y) :
    Tendsto (fun n => (f (w (n+1))-f (w 0))/((n+1:ℕ):ℝ)) atTop (𝓝 0) := by
  have hu : Tendsto (fun n : ℕ => (2*B)/((n+1:ℕ):ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (2*B))
  have hbound (n : ℕ) : |(f (w (n+1))-f (w 0))/((n+1:ℕ):ℝ)| ≤ (2*B)/((n+1:ℕ):ℝ) := by
    rw [abs_div,abs_of_pos (show (0:ℝ)<((n+1:ℕ):ℝ) by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (abs_sub _ _).trans ((add_le_add (hb _) (hb _)).trans_eq (by ring))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero (fun n => abs_nonneg _) hbound hu

theorem telescope (K : Kernel Y Y) [IsMarkovKernel K] (f : Y → ℝ) (n : ℕ) (w : ℕ → Y) :
    average (predict K f) n w-average f n w =
      (f (w (n+1))-f (w 0))/((n+1:ℕ):ℝ) -
      (∑ t ∈ Finset.range (n+1),innovation K f t w)/((n+1:ℕ):ℝ) := by
  have ht : (∑ t ∈ Finset.range (n+1),(f (w (t+1))-f (w t))) =
      f (w (n+1))-f (w 0) := Finset.sum_range_sub (fun t => f (w t)) (n+1)
  rw [← ht]
  simp only [average,innovation,Finset.sum_sub_distrib]
  ring

theorem conditional_predict_integral (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure)
    (f : Y → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, |f y| ≤ B) :
    ∀ᵐ w ∂canonicalPathLaw K π.toMeasure,
      (∫ y, predict K f y ∂(randomLaw K π w).toMeasure) =
        ∫ y, f y ∂(randomLaw K π w).toMeasure := by
  filter_upwards [state_average_tendsto K π hπ f hf B hB hb,
    state_average_tendsto K π hπ (predict K f) (predict_measurable K f hf) B hB (predict_bound K f B hb),
    canonical_innovation_strong_law K π f hf B hB hb] with w hfav hKav hi
  have hd := hKav.sub hfav
  have hz := (endpoint_tendsto f B hb w).sub hi
  have he : (fun n => average (predict K f) n w-average f n w) =
      (fun n => (f (w (n+1))-f (w 0))/((n+1:ℕ):ℝ) -
        (∑ t ∈ Finset.range (n+1),innovation K f t w)/((n+1:ℕ):ℝ)) :=
    funext fun n => telescope K f n w
  simp only [sub_zero] at hz
  rw [← he] at hz
  have hzero := tendsto_nhds_unique hd hz
  exact sub_eq_zero.mp hzero

def ambientKernel (K : Kernel Y Y) [IsMarkovKernel K] (π : ProbabilityMeasure Y) :
    Kernel (ℕ → Y) Y :=
  (conditionalKernel K π).comap id
    (measurable_id'' (Hopf.invariantSigma_le StationaryCanonical.shift))

instance ambientKernel_isMarkov (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) : IsMarkovKernel (ambientKernel K π) := by
  unfold ambientKernel
  infer_instance

theorem ambientKernel_apply (K : Kernel Y Y) [IsMarkovKernel K] (π : ProbabilityMeasure Y) (w : ℕ → Y) :
    ambientKernel K π w = (randomLaw K π w).toMeasure := rfl

theorem composed_kernel_ae_eq (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure) :
    (K ∘ₖ ambientKernel K π) =ᵐ[canonicalPathLaw K π.toMeasure] ambientKernel K π := by
  apply kernel_ae_eq_of_measurable_evaluations
  intro E hE
  let f : Y → ℝ := E.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hE
  have hb (y : Y) : |f y| ≤ 1 := by by_cases hy : y ∈ E <;> simp [f,hy]
  filter_upwards [conditional_predict_integral K π hπ f hf 1 (by norm_num) hb] with w hw
  have hint : Integrable f ((K ∘ₖ ambientKernel K π) w) :=
    Hopf.integrable_of_abs_bound hf 1 hb
  have he : (∫ y, f y ∂(K ∘ₖ ambientKernel K π) w) =
      ∫ y, f y ∂ambientKernel K π w := by
    rw [Kernel.integral_comp hint,ambientKernel_apply]
    exact hw
  have hr : ((K ∘ₖ ambientKernel K π) w).real E = (ambientKernel K π w).real E := by
    simpa only [f,integral_indicator_const (1:ℝ) hE,smul_eq_mul,mul_one] using he
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hr

theorem randomLaw_invariant_ae (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) (hπ : K ∘ₘ π.toMeasure = π.toMeasure) :
    ∀ᵐ w ∂canonicalPathLaw K π.toMeasure,
      K ∘ₘ (randomLaw K π w).toMeasure = (randomLaw K π w).toMeasure := by
  filter_upwards [composed_kernel_ae_eq K π hπ] with w hw
  exact hw

end
end PermanssonResearch.MultipleLimit.StationaryConditionalInvariant
