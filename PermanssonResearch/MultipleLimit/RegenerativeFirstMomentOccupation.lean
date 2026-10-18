import PermanssonResearch.MultipleLimit.RegenerativeDescriptorMoments
import PermanssonResearch.Probability.FirstMomentEmpiricalConvergence
import PermanssonResearch.Perturbation.FirstMomentOccupationProperty

/-! Genuine empirical W1 convergence for a nonfinite regenerative model
with an integrable regenerative descriptor reward. The countable scalar
laws are proved from the actual canonical process; the global occupation
selector and its fallback are fixed independently of all compared kernels. -/

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction ProbabilityTheory
namespace PermanssonResearch.MultipleLimit.RegenerativeFirstMoment
open FiniteCanonicalPath RegenerativeDescriptorMoments
open PermanssonResearch.Probability PermanssonResearch.Probability.Regenerative
open PermanssonResearch.Perturbation
set_option autoImplicit false
variable {Y V : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable [MetricSpace V] [MeasurableSpace V] [BorelSpace V] [SeparableSpace V] [Nonempty V]

theorem canonical_descriptor_empirical_tendsto
    (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (h : Y → V) (hh : Measurable h) (v₀ : V)
    (hbudget : RegenerativeMoment.RewardCondition R ξ r (fun y => dist (h y) v₀)) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => FirstMomentEmpirical.empirical v₀ n (fun t => h (w t))) atTop
        (𝓝 (target R ξ hr hr1 h hh v₀ hbudget)) := by
  have he := ae_all_iff.mpr (fun k => error_averages R K ξ μ hr hr1 hmix h hh v₀ hbudget k)
  have hc := ae_all_iff.mpr (fun k => ae_all_iff.mpr
    (fun i => cell_averages R K ξ μ hr hr1 hmix h hh v₀ hbudget k i))
  filter_upwards [he,hc] with w hwerr hwcell
  apply FirstMomentEmpirical.empirical_tendsto_of_quantized_averages
    v₀ (target R ξ hr hr1 h hh v₀ hbudget) (fun t => h (w t)) hwerr
  intro k i
  simpa only [FirstMomentEmpirical.cellIndicator] using! hwcell k i

theorem canonical_descriptor_weak_tendsto
    (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (h : Y → V) (hh : Measurable h) (v₀ : V)
    (hbudget : RegenerativeMoment.RewardCondition R ξ r (fun y => dist (h y) v₀)) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => FiniteStateOccupation.empiricalOccupation (fun t => h (w t))
        (n+1) (Nat.succ_pos n)) atTop (𝓝 ((target R ξ hr hr1 h hh v₀ hbudget).probability)) := by
  filter_upwards [canonical_descriptor_empirical_tendsto R K ξ μ hr hr1 hmix h hh v₀ hbudget]
    with w hw
  have ht := FirstMomentProbability.probability_continuous.continuousAt.tendsto.comp hw
  simpa only [Function.comp_apply,FirstMomentEmpirical.empirical_probability] using! ht

variable [CompleteSpace V]

theorem occupationLimit_ae (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (h : Y → V) (hh : Measurable h) (v₀ : V)
    (hbudget : RegenerativeMoment.RewardCondition R ξ r (fun y => dist (h y) v₀))
    (fallback : FirstMomentProbability v₀) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      FirstMomentOccupation.occupationLimit v₀ h fallback w = target R ξ hr hr1 h hh v₀ hbudget := by
  filter_upwards [canonical_descriptor_empirical_tendsto R K ξ μ hr hr1 hmix h hh v₀ hbudget]
    with w hw
  exact FirstMomentOccupation.occupationLimit_of_tendsto v₀ h fallback _ w hw

theorem canonical_property_factor
    (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (h : Y → V) (hh : Measurable h) (v₀ : V)
    (hbudget : RegenerativeMoment.RewardCondition R ξ r (fun y => dist (h y) v₀))
    (fallback : FirstMomentProbability v₀) (Φ : FirstMomentProbability v₀ →ᵇ ℝ) :
    FirstMomentOccupation.property v₀ h fallback Φ
      ⟨canonicalPathLaw K μ.toMeasure,inferInstance⟩ = Φ (target R ξ hr hr1 h hh v₀ hbudget) := by
  apply FirstMomentOccupation.property_factor_of_ae_empirical_limit
  exact canonical_descriptor_empirical_tendsto R K ξ μ hr hr1 hmix h hh v₀ hbudget

end PermanssonResearch.MultipleLimit.RegenerativeFirstMoment
