import PermanssonResearch.Perturbation.GeneratedInvariantPerturbation

/-! The inclusive zero-contraction case on the infinite ambient real line. -/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.Perturbation.FirstMomentInvariantRegression
open PermanssonResearch.Probability FirstMomentInvariant
set_option autoImplicit false

noncomputable def reset : Kernel ℝ ℝ := Kernel.const ℝ (Measure.dirac 0)

instance reset_markov : IsMarkovKernel reset := by unfold reset; infer_instance

theorem reset_comp (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    reset ∘ₘ μ = Measure.dirac 0 := by simp [reset]

theorem reset_preserves : PreservesFirstMoment reset 0 := by
  have hrow : ∀ x, Integrable (fun y : ℝ => dist y 0) (reset x) := by
    intro x
    change Integrable (fun y : ℝ => dist y 0) (Measure.dirac 0)
    exact integrable_dirac (by simp)
  apply preservesFirstMoment_of_drift reset 0 hrow 0 0
  intro x
  change (∫ y : ℝ, dist y 0 ∂Measure.dirac 0) ≤ _
  simp

theorem reset_global_contraction : IsW1Contraction reset 0 := by
  intro μ ν hμ hν c hc
  letI : IsProbabilityMeasure μ := hμ
  letI : IsProbabilityMeasure ν := hν
  rw [reset_comp,reset_comp]
  simpa only [zero_mul] using W1DualLE.refl (Measure.dirac (0 : ℝ))

theorem reset_unique_invariant :
    ∃! π : FirstMomentProbability (0 : ℝ), Kernel.Invariant reset π.measure :=
  exists_unique_invariant reset 0 reset_preserves (show (0 : ℝ) ≤ 0 from le_rfl)
    (by norm_num) reset_global_contraction

theorem reset_actual_stationary_law :
    (stationary reset 0 reset_preserves (show (0 : ℝ) ≤ 0 from le_rfl)
      (by norm_num) reset_global_contraction).measure = Measure.dirac 0 := by
  have h := stationary_invariant reset 0 reset_preserves (show (0 : ℝ) ≤ 0 from le_rfl)
    (by norm_num) reset_global_contraction
  change reset ∘ₘ _ = _ at h
  rw [reset_comp] at h
  exact h.symm

theorem reset_all_initial_geometric_bound (μ : FirstMomentProbability (0 : ℝ)) (n : ℕ) :
    let π := stationary reset 0 reset_preserves (show (0 : ℝ) ≤ 0 from le_rfl)
      (by norm_num) reset_global_contraction
    couplingW1 (iterateLaw reset μ.measure n) π.measure ≤
      (0 : ℝ)^n * couplingW1 μ.measure π.measure := by
  apply actual_iterate_coupling_bound reset reset_preserves (show (0 : ℝ) ≤ 0 from le_rfl)
    reset_global_contraction
  exact stationary_invariant reset 0 reset_preserves (show (0 : ℝ) ≤ 0 from le_rfl)
    (by norm_num) reset_global_contraction

end PermanssonResearch.Perturbation.FirstMomentInvariantRegression
