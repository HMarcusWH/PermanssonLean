import PermanssonResearch.Probability.FirstMomentCompleteness
import PermanssonResearch.MultipleLimit.CountableEmpiricalWeak
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! The literal original finite empirical law in the complete first-moment
transport space. Its dependence on finitely many samples is continuous. -/

open MeasureTheory Filter TopologicalSpace
open scoped Topology BigOperators

namespace PermanssonResearch.Probability.FirstMomentEmpirical

set_option autoImplicit false
variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V] [SeparableSpace V]

noncomputable def finiteSample (v₀ : V) (n : ℕ) (z : Fin (n+1) → V) :
    FirstMomentProbability v₀ where
  probability := (PermanssonLean.RegimeSpecification.uniformFinProbability
    (n+1) (Nat.succ_pos n)).map z
  firstMoment := by
    apply (integrable_map_measure (measurable_id.dist measurable_const).aestronglyMeasurable
      (measurable_of_finite z).aemeasurable).2
    exact Integrable.of_finite

theorem integral_finiteSample (v₀ : V) (n : ℕ) (z : Fin (n+1) → V)
    (f : V → ℝ) (hf : Measurable f) :
    (∫ v, f v ∂(finiteSample v₀ n z).measure) =
      ((n+1 : ℕ) : ℝ)⁻¹ * ∑ i, f (z i) := by
  change (∫ v, f v ∂Measure.map z
    (PermanssonLean.RegimeSpecification.uniformFinProbability (n+1) (Nat.succ_pos n)).toMeasure) = _
  rw [integral_map (measurable_of_finite z).aemeasurable hf.aestronglyMeasurable,
    MultipleLimit.FiniteUniformAverage.integral_uniformFin_eq_average]

theorem finiteSample_distance_le (v₀ : V) (n : ℕ) (z z' : Fin (n+1) → V) :
    dist (finiteSample v₀ n z) (finiteSample v₀ n z') ≤
      ((n+1 : ℕ) : ℝ)⁻¹ * ∑ i, dist (z i) (z' i) := by
  apply FirstMomentProbability.distance_le
  intro f hf
  rw [integral_finiteSample _ _ _ _ hf.measurable,
    integral_finiteSample _ _ _ _ hf.measurable, ← mul_sub, ← Finset.sum_sub_distrib,
    abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hf.lipschitz.dist_le_mul (z i) (z' i)

theorem finiteSample_lipschitz (v₀ : V) (n : ℕ) : LipschitzWith 1 (finiteSample v₀ n) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  rw [NNReal.coe_one, one_mul]
  apply (finiteSample_distance_le v₀ n z z').trans
  have hs : (∑ i : Fin (n+1), dist (z i) (z' i)) ≤
      ((n+1 : ℕ) : ℝ) * dist z z' := by
    calc
      _ ≤ ∑ _i : Fin (n+1), dist z z' :=
        Finset.sum_le_sum (fun i _ => dist_le_pi_dist z z' i)
      _ = _ := by simp
  calc
    _ ≤ ((n+1 : ℕ) : ℝ)⁻¹ * (((n+1 : ℕ) : ℝ) * dist z z') :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

noncomputable def empirical (v₀ : V) (n : ℕ) (w : ℕ → V) : FirstMomentProbability v₀ :=
  finiteSample v₀ n (fun i => w (i : ℕ))

theorem empirical_probability (v₀ : V) (n : ℕ) (w : ℕ → V) :
    (empirical v₀ n w).probability =
      MultipleLimit.FiniteStateOccupation.empiricalOccupation w (n+1) (Nat.succ_pos n) := rfl

theorem empirical_integral (v₀ : V) (n : ℕ) (w : ℕ → V) (f : V → ℝ) (hf : Measurable f) :
    (∫ v, f v ∂(empirical v₀ n w).measure) =
      (∑ t ∈ Finset.range (n+1), f (w t))/((n+1 : ℕ) : ℝ) :=
  MultipleLimit.CountableEmpirical.empirical_integral w n f hf

theorem empirical_stronglyMeasurable (v₀ : V) (n : ℕ) :
    StronglyMeasurable (empirical v₀ n) := by
  exact (finiteSample_lipschitz v₀ n).continuous.stronglyMeasurable.comp_measurable
    (Measurable.of_eval (fun i : Fin (n+1) => measurable_pi_apply (i : ℕ)))

end PermanssonResearch.Probability.FirstMomentEmpirical
