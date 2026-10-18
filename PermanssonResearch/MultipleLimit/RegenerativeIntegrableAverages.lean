import PermanssonResearch.MultipleLimit.RegenerativeInitialTransfer
import PermanssonResearch.MultipleLimit.RegenerativeAverages
import PermanssonResearch.MultipleLimit.StationaryConditionalLaw
import PermanssonResearch.Probability.CesaroShiftInvariant
import PermanssonResearch.Probability.RegenerativeMomentCondition

/-! Integrable nonnegative regenerative rewards, including unbounded
descriptor distances. L1 maximal approximation is applied only to the
actual stationary law; regenerated common mass transfers the measurable
shift-invariant limit event to every initial law. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory
namespace PermanssonResearch.MultipleLimit.RegenerativeIntegrable
open FiniteCanonicalPath StationaryCanonical
open PermanssonResearch.Probability PermanssonResearch.Probability.Regenerative
set_option autoImplicit false
variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]

theorem integral_initial_coordinate (K : Kernel Y Y) [IsMarkovKernel K]
    (π : ProbabilityMeasure Y) {f : Y → ℝ} (hf : Measurable f) :
    (∫ w : ℕ → Y, f (w 0) ∂canonicalPathLaw K π.toMeasure) = ∫ y, f y ∂π.toMeasure := by
  rw [← integral_map (measurable_pi_apply 0).aemeasurable hf.aestronglyMeasurable,
    canonical_eval_zero]

theorem stationary_nonnegative_integrable_averages
    (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (f : Y → ℝ) (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) (hfi : Integrable f (law R ξ r)) :
    ∀ᵐ w ∂canonicalPathLaw K (probabilityLaw R ξ hr hr1).toMeasure,
      Tendsto (fun n => birkhoffAverage ℝ shift (fun q : ℕ → Y => f (q 0)) n w)
        atTop (𝓝 (∫ y, f y ∂law R ξ r)) := by
  let π := probabilityLaw R ξ hr hr1
  have hπ : K ∘ₘ π.toMeasure = π.toMeasure := law_invariant R K ξ hr hr1 hmix
  have hfpath : Measurable (fun w : ℕ → Y => f (w 0)) := hf.comp (measurable_pi_apply 0)
  have himap : Integrable f ((canonicalPathLaw K π.toMeasure).map (fun w : ℕ → Y => w 0)) := by
    rw [canonical_eval_zero]
    exact hfi
  have hipath : Integrable (fun w : ℕ → Y => f (w 0)) (canonicalPathLaw K π.toMeasure) :=
    (integrable_map_measure hf.aestronglyMeasurable (measurable_pi_apply 0).aemeasurable).mp himap
  have hav : ∀ k, ∀ᵐ w ∂canonicalPathLaw K π.toMeasure,
      Tendsto (fun n => birkhoffAverage ℝ shift
        (Hopf.positiveTruncation (fun q : ℕ → Y => f (q 0)) k) n w)
        atTop (𝓝 (∫ w : ℕ → Y, Hopf.positiveTruncation (fun q => f (q 0)) k w
          ∂canonicalPathLaw K π.toMeasure)) := by
    intro k
    let g : Y → ℝ := Hopf.positiveTruncation f k
    have hg : Measurable g := Hopf.positiveTruncation_measurable hf k
    have hb : ∀ y, |g y| ≤ (k : ℝ) := Hopf.positiveTruncation_bound hf0 k
    have he : (∫ w : ℕ → Y, Hopf.positiveTruncation (fun q => f (q 0)) k w
        ∂canonicalPathLaw K π.toMeasure) = ∫ y, g y ∂π.toMeasure :=
      integral_initial_coordinate K π hg
    rw [he]
    filter_upwards [Regenerative.canonical_regenerative_averages K R ξ π hr hr1 hmix
      hg (Nat.cast_nonneg k) hb] with w hw
    apply (tendsto_add_atTop_iff_nat 1).1
    change Tendsto (fun n => birkhoffAverage ℝ shift (fun q : ℕ → Y => g (q 0)) (n+1) w)
      atTop (𝓝 (∫ y, g y ∂law R ξ r))
    simpa only [StationaryConditional.state_average_eq_birkhoff] using! hw
  have h := Hopf.ae_nonnegative_average_limit (shift_measurePreserving K π hπ)
    (fun w : ℕ → Y => f (w 0)) hfpath hipath (fun w => hf0 (w 0)) hav
  rw [integral_initial_coordinate K π hf] at h
  exact h

theorem canonical_nonnegative_integrable_averages
    (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (f : Y → ℝ) (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) (hfi : Integrable f (law R ξ r)) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => (∑ t ∈ Finset.range (n+1), f (w t))/((n+1 : ℕ) : ℝ))
        atTop (𝓝 (∫ y, f y ∂law R ξ r)) := by
  let π := probabilityLaw R ξ hr hr1
  let c := ∫ y, f y ∂law R ξ r
  let fp : (ℕ → Y) → ℝ := fun w => f (w 0)
  let p : (ℕ → Y) → Prop := fun w =>
    Tendsto (fun n => birkhoffAverage ℝ shift fp n w) atTop (𝓝 c)
  have hp : MeasurableSet {w | p w} :=
    CesaroShift.average_limit_measurable measurable_shift (hf.comp (measurable_pi_apply 0)) c
  have hs : ∀ w, p (shift w) ↔ p w := fun w =>
    CesaroShift.average_limit_shift_iff shift fp w c
  have hπ : K ∘ₘ π.toMeasure = π.toMeasure := law_invariant R K ξ hr hr1 hmix
  have ht := RegenerativeTransfer.ae_shiftInvariant_transfer R K ξ μ π hr hr1 hmix hπ p hp hs
    (stationary_nonnegative_integrable_averages R K ξ hr hr1 hmix f hf hf0 hfi)
  filter_upwards [ht] with w hw
  have h := hw.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_apply,fp,c,← StationaryConditional.state_average_eq_birkhoff] using! h

theorem canonical_nonnegative_rewardCondition_averages
    (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (f : Y → ℝ) (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) (hbudget : RegenerativeMoment.RewardCondition R ξ r f) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n => (∑ t ∈ Finset.range (n+1), f (w t))/((n+1 : ℕ) : ℝ))
        atTop (𝓝 (∫ y, f y ∂law R ξ r)) :=
  canonical_nonnegative_integrable_averages R K ξ μ hr hr1 hmix f hf hf0
    (RegenerativeMoment.integrable_law_of_rewardCondition R ξ hr hr1 hf hbudget)

end PermanssonResearch.MultipleLimit.RegenerativeIntegrable
