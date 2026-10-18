import PermanssonResearch.Probability.FirstMomentKantorovichDuality

/-! Regressions for the actual separable-space first-moment construction,
including laws on an infinite ambient space. -/

open MeasureTheory TopologicalSpace
namespace PermanssonResearch.Probability.FirstMomentTransportRegression
set_option autoImplicit false

variable {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable [SeparableSpace Y] [Nonempty Y]

theorem quantizer_zero (y₀ y : Y) : FirstMomentQuantization.quantizer y₀ 0 y = y₀ := by
  simp [FirstMomentQuantization.quantizer_eq_nearest,
    FirstMomentQuantization.nearestIndex,FirstMomentQuantization.centers]

theorem error_at_anchor (y₀ : Y) (n : ℕ) : FirstMomentQuantization.error y₀ n y₀ = 0 := by
  apply le_antisymm
  · simpa using FirstMomentQuantization.error_le_first_moment y₀ n y₀
  · exact FirstMomentQuantization.error_nonneg y₀ n y₀

theorem equal_firstMoment_laws_zero (μ : Measure Y) [IsProbabilityMeasure μ]
    (y₀ : Y) (hμ : Integrable (fun y => dist y y₀) μ) : couplingW1 μ μ = 0 := by
  apply le_antisymm
  · exact firstMoment_couplingW1_le_of_w1DualLE μ μ y₀ hμ hμ (W1DualLE.refl μ)
  · exact (firstMoment_w1DualLE_couplingW1 μ μ y₀ hμ hμ).nonneg

/-- The original dual and coupling distance agree on genuinely infinite
ambient space, with no finite-state typeclass assumption. -/
theorem real_dirac_distance_three :
    couplingW1 (Measure.dirac (0 : ℝ)) (Measure.dirac 3) = 3 := by
  have hμ : Integrable (fun y : ℝ => dist y 0) (Measure.dirac 0) :=
    integrable_dirac (by simp)
  have hν : Integrable (fun y : ℝ => dist y 0) (Measure.dirac 3) :=
    integrable_dirac (by simp)
  have hd : W1DualLE (Measure.dirac (0 : ℝ)) (Measure.dirac 3) 3 := by
    intro f hf
    simpa [Real.dist_eq] using hf.lipschitz.dist_le_mul (0 : ℝ) 3
  apply le_antisymm
  · exact firstMoment_couplingW1_le_of_w1DualLE _ _ 0 hμ hν hd
  · let f : ℝ → ℝ := fun y => max (min y 3) 0
    have hl : LipschitzWith 1 f := (LipschitzWith.id.min_const 3).max_const 0
    have hf : IsKRTest f := by
      refine ⟨hl.continuous.measurable,hl,⟨3,fun y => ?_⟩⟩
      apply abs_le.mpr
      constructor
      · have h : 0 ≤ max (min y 3) 0 := le_max_right _ _
        dsimp [f]
        linarith
      · exact max_le (min_le_right _ _) (by norm_num)
    have h := firstMoment_w1DualLE_couplingW1 (Measure.dirac (0 : ℝ))
      (Measure.dirac 3) 0 hμ hν f hf
    simpa [f] using h

theorem real_bound_two_rejected :
    ¬ W1DualLE (Measure.dirac (0 : ℝ)) (Measure.dirac 3) 2 := by
  intro h
  have hh := firstMoment_couplingW1_le_of_w1DualLE _ _ 0
    (integrable_dirac (by simp)) (integrable_dirac (by simp)) h
  rw [real_dirac_distance_three] at hh
  norm_num at hh

end PermanssonResearch.Probability.FirstMomentTransportRegression
