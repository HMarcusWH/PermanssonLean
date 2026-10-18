import PermanssonResearch.Probability.FirstMomentQuantization
import PermanssonResearch.Probability.FiniteLipschitzExtension
import PermanssonResearch.Probability.FinitePartitionCoupling

/-! First-moment KR identification by actual finite approximation and lifting.
Separability and Borel measurability suffice for this infimum identification;
no completeness or optimal-coupling hypothesis is imposed. -/

open MeasureTheory Filter TopologicalSpace
open scoped Topology
namespace PermanssonResearch.Probability.FirstMomentKR
open ActionTrace
set_option autoImplicit false
variable {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable [SeparableSpace Y] [Nonempty Y]

/-- Every approximation uses a real finite transport plan and lifts it to
an actual coupling of the original laws. -/
theorem exists_approximate_coupling (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (y₀ : Y)
    (hμ : Integrable (fun y => dist y y₀) μ) (hν : Integrable (fun y => dist y y₀) ν)
    {b : ℝ} (hb : W1DualLE μ ν b) (n : ℕ) :
    ∃ γ : IntegrableCoupling μ ν, γ.cost ≤ b+2*((∫ y,
      FirstMomentQuantization.error y₀ n y ∂μ)+
      (∫ y, FirstMomentQuantization.error y₀ n y ∂ν)) := by
  classical
  let c : Fin (n+1) → Y := FirstMomentQuantization.center y₀ n
  let t : Y → Fin (n+1) := FirstMomentQuantization.finiteIndex
    (FirstMomentQuantization.centers y₀) n
  have ht : Measurable t := FirstMomentQuantization.finiteIndex_measurable _ _
  have heμ : Integrable (fun y => dist y (c (t y))) μ :=
    FirstMomentQuantization.error_integrable μ y₀ hμ n
  have heν : Integrable (fun y => dist y (c (t y))) ν :=
    FirstMomentQuantization.error_integrable ν y₀ hν n
  letI : PseudoMetricSpace (Fin (n+1)) := PseudoMetricSpace.induced c inferInstance
  have hfinite : W1DualLE (μ.map t) (ν.map t)
      (b+(∫ y, dist y (c (t y)) ∂μ)+(∫ y, dist y (c (t y)) ∂ν)) :=
    FiniteLipschitzExtension.finite_pushforward_dual_bound μ ν c t ht heμ heν hb
  obtain ⟨g,hgμ,hgν,hgc⟩ := FiniteTransport.exists_plan_of_w1DualLE
    (μ.map t) (ν.map t) hfinite
  have hrow : ∀ i, ∑ j, g.mass (i,j) = μ.real (t ⁻¹' {i}) := by
    intro i
    rw [hgμ i]
    exact congrArg ENNReal.toReal (Measure.map_apply ht (measurableSet_singleton i))
  have hcol : ∀ j, ∑ i, g.mass (i,j) = ν.real (t ⁻¹' {j}) := by
    intro j
    rw [hgν j]
    exact congrArg ENNReal.toReal (Measure.map_apply ht (measurableSet_singleton j))
  obtain ⟨γ,hγ⟩ := exists_finite_partition_coupling μ ν y₀ hμ hν t ht g hrow hcol c
  refine ⟨γ,?_⟩
  change g.expect (fun ij => dist (c ij.1) (c ij.2)) ≤
    b+(∫ y, dist y (c (t y)) ∂μ)+(∫ y, dist y (c (t y)) ∂ν) at hgc
  change γ.cost ≤ b+2*((∫ y, dist y (c (t y)) ∂μ)+
    (∫ y, dist y (c (t y)) ∂ν))
  linarith

end PermanssonResearch.Probability.FirstMomentKR

namespace PermanssonResearch.Probability
set_option autoImplicit false
variable {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable [SeparableSpace Y]

/-- Genuine reverse KR for probability laws on a separable Borel metric
space with finite first moments, on the original `W1DualLE` interface. -/
theorem firstMoment_couplingW1_le_of_w1DualLE (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (y₀ : Y)
    (hμ : Integrable (fun y => dist y y₀) μ) (hν : Integrable (fun y => dist y y₀) ν)
    {b : ℝ} (hb : W1DualLE μ ν b) : couplingW1 μ ν ≤ b := by
  haveI : Nonempty Y := ⟨y₀⟩
  have hbound : ∀ n : ℕ, couplingW1 μ ν ≤ b+2*((∫ y,
      FirstMomentQuantization.error y₀ n y ∂μ)+
      (∫ y, FirstMomentQuantization.error y₀ n y ∂ν)) := by
    intro n
    obtain ⟨γ,hγ⟩ := FirstMomentKR.exists_approximate_coupling μ ν y₀ hμ hν hb n
    have hcost : BddBelow (couplingCosts μ ν) :=
      ⟨0,by rintro x ⟨η,rfl⟩; exact η.cost_nonneg⟩
    exact (csInf_le hcost (show γ.cost ∈ couplingCosts μ ν from ⟨γ,rfl⟩)).trans hγ
  have ht := (FirstMomentQuantization.integral_error_tendsto μ y₀ hμ).add
    (FirstMomentQuantization.integral_error_tendsto ν y₀ hν)
  have ht' := (tendsto_const_nhds (x := b)).add (ht.const_mul 2)
  have ht'' : Tendsto (fun n => b+2*((∫ y, FirstMomentQuantization.error y₀ n y ∂μ)+
      (∫ y, FirstMomentQuantization.error y₀ n y ∂ν))) atTop (𝓝 b) := by
    simpa using ht'
  exact ge_of_tendsto' ht'' hbound

theorem firstMoment_coupling_nonempty (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (y₀ : Y)
    (hμ : Integrable (fun y => dist y y₀) μ) (hν : Integrable (fun y => dist y y₀) ν) :
    Nonempty (IntegrableCoupling μ ν) := by
  haveI : Nonempty Y := ⟨y₀⟩
  obtain ⟨γ,_⟩ := FirstMomentKR.exists_approximate_coupling μ ν y₀ hμ hν
    (W1DualLE.of_integrable_dist μ ν y₀ hμ hν) 0
  exact ⟨γ⟩

theorem firstMoment_w1DualLE_couplingW1 (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (y₀ : Y)
    (hμ : Integrable (fun y => dist y y₀) μ) (hν : Integrable (fun y => dist y y₀) ν) :
    W1DualLE μ ν (couplingW1 μ ν) :=
  w1DualLE_couplingW1 μ ν (firstMoment_coupling_nonempty μ ν y₀ hμ hν)

theorem firstMoment_w1DualLE_iff_couplingW1_le (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (y₀ : Y)
    (hμ : Integrable (fun y => dist y y₀) μ) (hν : Integrable (fun y => dist y y₀) ν)
    (b : ℝ) : W1DualLE μ ν b ↔ couplingW1 μ ν ≤ b :=
  ⟨firstMoment_couplingW1_le_of_w1DualLE μ ν y₀ hμ hν,
    fun h => (firstMoment_w1DualLE_couplingW1 μ ν y₀ hμ hν).mono h⟩

theorem firstMoment_couplingW1_eq_dual_supremum (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (y₀ : Y)
    (hμ : Integrable (fun y => dist y y₀) μ) (hν : Integrable (fun y => dist y y₀) ν) :
    couplingW1 μ ν = sSup (krDualValues μ ν) := by
  have hne : (krDualValues μ ν).Nonempty :=
    ⟨0,(fun _ => 0),IsKRTest.zero,by simp⟩
  have hb : BddAbove (krDualValues μ ν) := by
    refine ⟨couplingW1 μ ν,?_⟩
    rintro x ⟨f,hf,rfl⟩
    exact firstMoment_w1DualLE_couplingW1 μ ν y₀ hμ hν f hf
  apply le_antisymm
  · apply firstMoment_couplingW1_le_of_w1DualLE μ ν y₀ hμ hν
    intro f hf
    exact le_csSup hb ⟨f,hf,rfl⟩
  · apply csSup_le hne
    rintro x ⟨f,hf,rfl⟩
    exact firstMoment_w1DualLE_couplingW1 μ ν y₀ hμ hν f hf

end PermanssonResearch.Probability
