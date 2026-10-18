import PermanssonResearch.Probability.FirstMomentMetric
import PermanssonResearch.Probability.GluedCouplingSequence
import PermanssonResearch.Probability.SummableStepLimit

/-! Actual transport limits from a summable sequence of adjacent couplings. -/

open MeasureTheory Filter TopologicalSpace
open scoped Topology
namespace PermanssonResearch.Probability.FirstMomentProbability
set_option autoImplicit false

variable {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [MeasurableSpace Y]
variable [BorelSpace Y] [SeparableSpace Y] {y₀ : Y}

theorem exists_limit_of_summable_couplings (μ : ℕ → FirstMomentProbability y₀)
    (γ : ∀ n, IntegrableCoupling (μ n).measure (μ (n+1)).measure)
    (hs : Summable (fun n => (γ n).cost)) :
    ∃ ν : FirstMomentProbability y₀,
      (∀ n, dist (μ n) ν ≤ ∑' k, (γ (n+k)).cost) ∧
      Tendsto μ atTop (𝓝 ν) := by
  haveI : Nonempty Y := ⟨y₀⟩
  let m : ℕ → Measure Y := fun n => (μ n).measure
  let P : Measure (ℕ → Y) := GluedCouplingSequence.law m γ
  haveI : IsProbabilityMeasure P := GluedCouplingSequence.law_probability m γ
  let X : ℕ → (ℕ → Y) → Y := fun n w => w n
  have hm : ∀ n, Measurable (X n) := fun n => measurable_pi_apply n
  have hi : ∀ n, Integrable (SummableStepLimit.step X n) P :=
    fun n => GluedCouplingSequence.step_integrable m γ n
  have he (n : ℕ) : (∫ w, SummableStepLimit.step X n w ∂P) = (γ n).cost :=
    GluedCouplingSequence.integral_step m γ n
  have hs' : Summable (fun n => ∫ w, SummableStepLimit.step X n w ∂P) := by
    simpa only [he] using hs
  let L : (ℕ → Y) → Y := SummableStepLimit.limit X
  have hL : Measurable L := SummableStepLimit.limit_measurable X hm
  have h₀ : Integrable (fun w => dist (X 0 w) y₀) P := by
    have h : Integrable (fun y => dist y y₀) (P.map (X 0)) := by
      rw [GluedCouplingSequence.marginal m γ 0]
      exact (μ 0).firstMoment
    exact h.comp_measurable (hm 0)
  have hfirst : Integrable (fun y => dist y y₀) (P.map L) := by
    apply (integrable_map_measure (measurable_id.dist measurable_const).aestronglyMeasurable
      hL.aemeasurable).2
    exact SummableStepLimit.limit_firstMoment P X hm hi hs' y₀ h₀
  let ν : FirstMomentProbability y₀ := ⟨⟨P.map L,inferInstance⟩,hfirst⟩
  have hb (n : ℕ) : dist (μ n) ν ≤ ∑' k, (γ (n+k)).cost := by
    let q : (ℕ → Y) → Y × Y := fun w => (X n w,L w)
    have hq : Measurable q := (hm n).prodMk hL
    have hcost : Integrable (fun z : Y × Y => dist z.1 z.2) (P.map q) := by
      apply (integrable_map_measure (measurable_fst.dist measurable_snd).aestronglyMeasurable
        hq.aemeasurable).2
      exact SummableStepLimit.dist_limit_integrable P X hm hi hs' n
    let η : IntegrableCoupling (μ n).measure ν.measure := {
      law := P.map q
      isProbability := inferInstance
      first := by
        rw [Measure.map_map measurable_fst hq]
        exact GluedCouplingSequence.marginal m γ n
      second := by
        rw [Measure.map_map measurable_snd hq]
        rfl
      cost_integrable := hcost }
    apply distance_le
    apply η.dual_bound.mono
    change (∫ z, dist z.1 z.2 ∂P.map q) ≤ _
    rw [integral_map hq.aemeasurable
      (measurable_fst.dist measurable_snd).aestronglyMeasurable]
    simpa only [he] using SummableStepLimit.integral_dist_limit_le P X hm hi hs' n
  refine ⟨ν,hb,?_⟩
  apply tendsto_iff_dist_tendsto_zero.2
  apply squeeze_zero (fun n => dist_nonneg) hb
  have heq : (fun n => ∑' k, (γ (n+k)).cost) =
      (fun n => ∑' k, (γ (k+n)).cost) := by
    funext n
    apply tsum_congr
    intro k
    rw [Nat.add_comm]
  rw [heq]
  exact tendsto_sum_nat_add (fun n => (γ n).cost)

end PermanssonResearch.Probability.FirstMomentProbability
