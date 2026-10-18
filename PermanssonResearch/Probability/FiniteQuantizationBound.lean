import PermanssonResearch.Probability.FirstMomentMetric
import PermanssonResearch.Probability.FirstMomentQuantization

/-! Actual finite quantizer-cell decomposition of the original KR tests.
The center-distance coefficients are finite and independent of the test. -/

open MeasureTheory Filter TopologicalSpace
open scoped Topology BigOperators

namespace PermanssonResearch.Probability.FirstMomentEmpirical

noncomputable section
variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V]
  [SeparableSpace V] [Nonempty V]
open FirstMomentQuantization

def cellIndicator (v0 : V) (k : ℕ) (i : Fin (k+1)) (v : V) : ℝ :=
  if finiteIndex (centers v0) k v=i then 1 else 0

theorem cellIndicator_measurable (v0 : V) (k : ℕ) (i : Fin (k+1)) :
    Measurable (cellIndicator v0 k i) :=
  Measurable.ite (measurableSet_eq_fun (finiteIndex_measurable (centers v0) k)
    measurable_const) measurable_const measurable_const

theorem cellIndicator_integrable (μ : Measure V) [IsProbabilityMeasure μ]
    (v0 : V) (k : ℕ) (i : Fin (k+1)) : Integrable (cellIndicator v0 k i) μ := by
  apply Integrable.of_bound (cellIndicator_measurable v0 k i).aestronglyMeasurable 1
  exact ae_of_all _ (fun v => by simp [cellIndicator]; split_ifs <;> norm_num)

theorem quantized_integrable (μ : Measure V) [IsProbabilityMeasure μ]
    (v0 : V) (k : ℕ) (f : V → ℝ) (hf : IsKRTest f) :
    Integrable (fun v => f (quantizer v0 k v)) μ := by
  obtain ⟨C,hC⟩ := hf.bounded
  apply Integrable.of_bound (hf.measurable.comp (quantizer_measurable v0 k)).aestronglyMeasurable C
  exact ae_of_all _ (fun v => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hC (quantizer v0 k v))

theorem centered_quantized_integral (μ : Measure V) [IsProbabilityMeasure μ]
    (v0 : V) (k : ℕ) (f : V → ℝ) :
    (∫ v, f (quantizer v0 k v)-f v0 ∂μ) =
      ∑ i : Fin (k+1), (f (center v0 k i)-f v0)*(∫ v, cellIndicator v0 k i v ∂μ) := by
  classical
  have he (v : V) : f (quantizer v0 k v)-f v0 =
      ∑ i : Fin (k+1), (f (center v0 k i)-f v0)*cellIndicator v0 k i v := by
    simp [cellIndicator,quantizer]
  simp_rw [he]
  rw [integral_finset_sum _ (fun i _ => (cellIndicator_integrable μ v0 k i).const_mul _)]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_const_mul _ _

theorem quantized_integral_error (v0 : V) (μ : FirstMomentProbability v0)
    (k : ℕ) (f : V → ℝ) (hf : IsKRTest f) :
    |(∫ v, f v ∂μ.measure)-(∫ v, f (quantizer v0 k v) ∂μ.measure)| ≤
      ∫ v, error v0 k v ∂μ.measure := by
  have hi := hf.integrable μ.measure
  have hq := quantized_integrable μ.measure v0 k f hf
  rw [← integral_sub hi hq]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono (hi.sub hq).abs (error_integrable μ.measure v0 μ.firstMoment k)
  intro v
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul,error,Pi.sub_apply] using
    hf.lipschitz.dist_le_mul v (quantizer v0 k v)

/-- A genuine P1 distance bound from two quantization errors and finitely many
actual cell-mass differences, with no transport or convergence premise. -/
theorem distance_le_quantization (v0 : V) (μ ν : FirstMomentProbability v0) (k : ℕ) :
    dist μ ν ≤ (∫ v, error v0 k v ∂μ.measure)+(∫ v, error v0 k v ∂ν.measure)+
      ∑ i : Fin (k+1), dist (center v0 k i) v0 *
        |(∫ v, cellIndicator v0 k i v ∂μ.measure)-(∫ v, cellIndicator v0 k i v ∂ν.measure)| := by
  apply FirstMomentProbability.distance_le
  intro f hf
  have hqμ := quantized_integrable μ.measure v0 k f hf
  have hqν := quantized_integrable ν.measure v0 k f hf
  have hμ : (∫ v, f (quantizer v0 k v) ∂μ.measure)-f v0 =
      ∑ i : Fin (k+1), (f (center v0 k i)-f v0)*(∫ v, cellIndicator v0 k i v ∂μ.measure) := by
    have h := centered_quantized_integral μ.measure v0 k f
    rw [integral_sub hqμ (integrable_const _)] at h
    simpa using h
  have hν : (∫ v, f (quantizer v0 k v) ∂ν.measure)-f v0 =
      ∑ i : Fin (k+1), (f (center v0 k i)-f v0)*(∫ v, cellIndicator v0 k i v ∂ν.measure) := by
    have h := centered_quantized_integral ν.measure v0 k f
    rw [integral_sub hqν (integrable_const _)] at h
    simpa using h
  have he : (∫ v, f (quantizer v0 k v) ∂μ.measure)-
      (∫ v, f (quantizer v0 k v) ∂ν.measure) =
      ∑ i : Fin (k+1), (f (center v0 k i)-f v0)*
        ((∫ v, cellIndicator v0 k i v ∂μ.measure)-(∫ v, cellIndicator v0 k i v ∂ν.measure)) := by
    calc
      _ = ((∫ v, f (quantizer v0 k v) ∂μ.measure)-f v0)-
          ((∫ v, f (quantizer v0 k v) ∂ν.measure)-f v0) := by ring
      _ = _ := by rw [hμ,hν,← Finset.sum_sub_distrib]; congr 1; funext i; ring
  have hs : |(∫ v, f (quantizer v0 k v) ∂μ.measure)-
      (∫ v, f (quantizer v0 k v) ∂ν.measure)| ≤
      ∑ i : Fin (k+1), dist (center v0 k i) v0 *
        |(∫ v, cellIndicator v0 k i v ∂μ.measure)-(∫ v, cellIndicator v0 k i v ∂ν.measure)| := by
    rw [he]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hf.lipschitz.dist_le_mul (center v0 k i) v0
  have hμe := quantized_integral_error v0 μ k f hf
  have hνe := quantized_integral_error v0 ν k f hf
  have h₁ := abs_sub_le (∫ v, f v ∂μ.measure)
    (∫ v, f (quantizer v0 k v) ∂μ.measure) (∫ v, f v ∂ν.measure)
  have h₂ := abs_sub_le (∫ v, f (quantizer v0 k v) ∂μ.measure)
    (∫ v, f (quantizer v0 k v) ∂ν.measure) (∫ v, f v ∂ν.measure)
  rw [abs_sub_comm (∫ v, f (quantizer v0 k v) ∂ν.measure) (∫ v, f v ∂ν.measure)] at h₂
  linarith

end
end PermanssonResearch.Probability.FirstMomentEmpirical
