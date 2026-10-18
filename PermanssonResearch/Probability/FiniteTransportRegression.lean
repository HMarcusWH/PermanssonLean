import PermanssonResearch.Probability.FiniteKantorovichDuality

/-! Exact transport regressions retain the given metric scale and include
degenerate laws. -/

open MeasureTheory
namespace PermanssonResearch.Probability.FiniteTransportRegression
set_option autoImplicit false
variable {Y : Type*} [Fintype Y] [PseudoMetricSpace Y] [MeasurableSpace Y]
variable [MeasurableSingletonClass Y]

theorem dirac_dual_bound (x y : Y) :
    W1DualLE (Measure.dirac x) (Measure.dirac y) (dist x y) := by
  intro f hf
  simpa [Real.dist_eq] using hf.lipschitz.dist_le_mul x y

theorem dirac_exact (x y : Y) :
    couplingW1 (Measure.dirac x) (Measure.dirac y) = dist x y := by
  haveI : Nonempty Y := ⟨x⟩
  apply le_antisymm
  · exact finite_couplingW1_le_of_w1DualLE _ _ (dirac_dual_bound x y)
  · have h := finite_w1DualLE_couplingW1 (Measure.dirac x) (Measure.dirac y)
      (fun z => dist x z) (FiniteTransport.finite_isKRTest (LipschitzWith.dist_right x))
    simpa [abs_of_nonneg dist_nonneg] using h

theorem equal_laws_zero (μ : Measure Y) [IsProbabilityMeasure μ] : couplingW1 μ μ = 0 := by
  apply le_antisymm
  · exact finite_couplingW1_le_of_w1DualLE μ μ (W1DualLE.refl μ)
  · exact (finite_w1DualLE_couplingW1 μ μ).nonneg

noncomputable def scaledMetric : MetricSpace Bool :=
  MetricSpace.induced (fun b : Bool => if b then (3 : ℝ) else 0) (by
    intro a b h
    cases a <;> cases b <;> norm_num at *) inferInstance

theorem scaled_two_point_exact :
    letI : MetricSpace Bool := scaledMetric
    letI : MeasurableSpace Bool := ⊤
    couplingW1 (Measure.dirac false) (Measure.dirac true) = 3 := by
  letI : MetricSpace Bool := scaledMetric
  letI : MeasurableSpace Bool := ⊤
  rw [dirac_exact]
  change dist (0 : ℝ) 3 = 3
  norm_num

/-- A distance-three witness rules out truncation by a common norm-one bound. -/
theorem scaled_two_point_bound_two_rejected :
    letI : MetricSpace Bool := scaledMetric
    letI : MeasurableSpace Bool := ⊤
    ¬ W1DualLE (Measure.dirac false) (Measure.dirac true) 2 := by
  letI : MetricSpace Bool := scaledMetric
  letI : MeasurableSpace Bool := ⊤
  intro h
  have hh := finite_couplingW1_le_of_w1DualLE _ _ h
  have he : couplingW1 (Measure.dirac false) (Measure.dirac true) = 3 :=
    scaled_two_point_exact
  rw [he] at hh
  norm_num at hh

end PermanssonResearch.Probability.FiniteTransportRegression
