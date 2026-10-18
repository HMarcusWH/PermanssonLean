import PermanssonResearch.Games.DiscountedTraceExpectation

/-! Every initial probability measure on a finite state space is represented exactly. -/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.ActionTrace
namespace Row
set_option autoImplicit false
universe u
variable {Y : Type u} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

noncomputable def ofMeasure (μ : Measure Y) [IsProbabilityMeasure μ] : Row Y where
  mass y := μ.real {y}
  nonneg _ := measureReal_nonneg
  total := by simpa using Measure.sum_measureReal_singleton (μ := μ) Finset.univ

@[simp] theorem ofMeasure_measure (μ : Measure Y) [IsProbabilityMeasure μ] :
    (ofMeasure μ).measure = μ := by
  classical
  apply Measure.ext_of_singleton
  intro y
  rw [measure_singleton]
  exact ENNReal.ofReal_toReal (measure_ne_top μ {y})

end Row
end PermanssonResearch.ActionTrace

namespace PermanssonResearch.DiscountedVerification
open ActionTrace
set_option autoImplicit false
universe u
variable {Y A : Type u} [Fintype Y] [Fintype A]
  [MeasurableSpace Y] [MeasurableSpace A]
  [DiscreteMeasurableSpace Y] [DiscreteMeasurableSpace A]

theorem expected_verification_initial_measure (G : Game Y A) (σ : BehavioralPolicy Y A)
    (μ : Measure Y) [IsProbabilityMeasure μ] (V : Y → ℝ) {R C : ℝ}
    (hR : ∀ y a b, |G.reward y a b| ≤ R) (hC : ∀ y, |V y| ≤ C)
    (hV : ∀ y a, Q G V y a ≤ V y) :
    (∫ w, (∑' n, G.discount^n * pathReward G n w)
      ∂canonicalLaw G σ (Row.ofMeasure μ)) ≤ ∫ y, V y ∂μ := by
  simpa only [Row.expect_eq_integral, Row.ofMeasure_measure] using
    expected_discounted_verification G σ (Row.ofMeasure μ) V hR hC hV

end PermanssonResearch.DiscountedVerification
