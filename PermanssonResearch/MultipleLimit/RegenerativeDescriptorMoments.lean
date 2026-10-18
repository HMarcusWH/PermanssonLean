import PermanssonResearch.MultipleLimit.RegenerativeIntegrableAverages
import PermanssonResearch.Probability.FirstMomentMetric
import PermanssonResearch.Probability.FirstMomentQuantization

/-! An actual first-moment descriptor law generated from a primitive
regenerative reward condition. All countably many quantizer errors and
finite-cell indicators satisfy the original canonical scalar averages,
for every initial probability. No descriptor-Markov assertion is used. -/

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology ProbabilityTheory
namespace PermanssonResearch.MultipleLimit.RegenerativeDescriptorMoments
open FiniteCanonicalPath RegenerativeIntegrable
open PermanssonResearch.Probability PermanssonResearch.Probability.Regenerative
set_option autoImplicit false
variable {Y V : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable [MetricSpace V] [MeasurableSpace V] [BorelSpace V] [SeparableSpace V] [Nonempty V]

noncomputable def target (R : Kernel Y Y) [IsMarkovKernel R] (ξ : ProbabilityMeasure Y)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (h : Y → V) (hh : Measurable h) (v₀ : V)
    (hbudget : RegenerativeMoment.RewardCondition R ξ r (fun y => dist (h y) v₀)) :
    FirstMomentProbability v₀ where
  probability := (probabilityLaw R ξ hr hr1).map h
  firstMoment := by
    change Integrable (fun v => dist v v₀) ((law R ξ r).map h)
    apply (integrable_map_measure (measurable_id.dist measurable_const).aestronglyMeasurable
      hh.aemeasurable).mpr
    exact RegenerativeMoment.integrable_law_of_rewardCondition R ξ hr hr1
      (hh.dist measurable_const) hbudget

theorem target_measure (R : Kernel Y Y) [IsMarkovKernel R] (ξ : ProbabilityMeasure Y)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (h : Y → V) (hh : Measurable h) (v₀ : V)
    (hbudget : RegenerativeMoment.RewardCondition R ξ r (fun y => dist (h y) v₀)) :
    (target R ξ hr hr1 h hh v₀ hbudget).measure = (law R ξ r).map h := rfl

theorem target_integral (R : Kernel Y Y) [IsMarkovKernel R] (ξ : ProbabilityMeasure Y)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (h : Y → V) (hh : Measurable h) (v₀ : V)
    (hbudget : RegenerativeMoment.RewardCondition R ξ r (fun y => dist (h y) v₀))
    {f : V → ℝ} (hf : Measurable f) :
    (∫ v, f v ∂(target R ξ hr hr1 h hh v₀ hbudget).measure) =
      ∫ y, f (h y) ∂law R ξ r := by
  rw [target_measure,integral_map hh.aemeasurable hf.aestronglyMeasurable]

theorem distance_averages (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (h : Y → V) (hh : Measurable h) (v₀ : V)
    (hbudget : RegenerativeMoment.RewardCondition R ξ r (fun y => dist (h y) v₀)) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => (∑ t ∈ Finset.range (n+1), dist (h (w t)) v₀)/((n+1 : ℕ) : ℝ))
        atTop (𝓝 (∫ v, dist v v₀ ∂(target R ξ hr hr1 h hh v₀ hbudget).measure)) := by
  rw [target_integral R ξ hr hr1 h hh v₀ hbudget
    (f := fun v => dist v v₀) (measurable_id.dist measurable_const)]
  exact canonical_nonnegative_rewardCondition_averages R K ξ μ hr hr1 hmix _
    (hh.dist measurable_const) (fun _ => dist_nonneg) hbudget

theorem error_averages (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (h : Y → V) (hh : Measurable h) (v₀ : V)
    (hbudget : RegenerativeMoment.RewardCondition R ξ r (fun y => dist (h y) v₀)) (k : ℕ) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => (∑ t ∈ Finset.range (n+1),
        FirstMomentQuantization.error v₀ k (h (w t)))/((n+1 : ℕ) : ℝ)) atTop
        (𝓝 (∫ v, FirstMomentQuantization.error v₀ k v
          ∂(target R ξ hr hr1 h hh v₀ hbudget).measure)) := by
  haveI : Nonempty V := ⟨v₀⟩
  have hd := RegenerativeMoment.integrable_law_of_rewardCondition R ξ hr hr1
    (hh.dist measurable_const) hbudget
  have he : Measurable (fun y => FirstMomentQuantization.error v₀ k (h y)) :=
    (FirstMomentQuantization.error_measurable v₀ k).comp hh
  have hei : Integrable (fun y => FirstMomentQuantization.error v₀ k (h y)) (law R ξ r) :=
    hd.mono' he.aestronglyMeasurable (ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (FirstMomentQuantization.error_nonneg v₀ k (h y))]
        using FirstMomentQuantization.error_le_first_moment v₀ k (h y))
  rw [target_integral R ξ hr hr1 h hh v₀ hbudget (FirstMomentQuantization.error_measurable v₀ k)]
  exact canonical_nonnegative_integrable_averages R K ξ μ hr hr1 hmix _ he
    (fun y => FirstMomentQuantization.error_nonneg v₀ k (h y)) hei

theorem cell_averages (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (h : Y → V) (hh : Measurable h) (v₀ : V)
    (hbudget : RegenerativeMoment.RewardCondition R ξ r (fun y => dist (h y) v₀))
    (k : ℕ) (i : Fin (k+1)) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => (∑ t ∈ Finset.range (n+1),
        if FirstMomentQuantization.finiteIndex (FirstMomentQuantization.centers v₀) k (h (w t))=i
        then (1 : ℝ) else 0)/((n+1 : ℕ) : ℝ)) atTop
        (𝓝 (∫ v, (if FirstMomentQuantization.finiteIndex
          (FirstMomentQuantization.centers v₀) k v=i then (1 : ℝ) else 0)
          ∂(target R ξ hr hr1 h hh v₀ hbudget).measure)) := by
  haveI : Nonempty V := ⟨v₀⟩
  let f : V → ℝ := fun v => if FirstMomentQuantization.finiteIndex
    (FirstMomentQuantization.centers v₀) k v=i then 1 else 0
  have hm : Measurable (FirstMomentQuantization.finiteIndex
      (FirstMomentQuantization.centers v₀) k) := FirstMomentQuantization.finiteIndex_measurable _ _
  have hf : Measurable f := Measurable.ite
    ((measurableSet_singleton i).preimage hm) measurable_const measurable_const
  rw [target_integral R ξ hr hr1 h hh v₀ hbudget hf]
  apply Regenerative.canonical_regenerative_averages K R ξ μ hr hr1 hmix (hf.comp hh)
    (M := 1) (by norm_num)
  intro y
  dsimp [f]
  split_ifs <;> norm_num

end PermanssonResearch.MultipleLimit.RegenerativeDescriptorMoments
