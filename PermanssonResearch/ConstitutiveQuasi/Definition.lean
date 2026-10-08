import PermanssonLean.Probability.FinitePrefixTV
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# CQ-1: bounded measurable finite-prefix properties

A horizon `L` means `L` transitions and coordinates `0, ..., L`.
This is a finite-horizon diagnostic, not an Exact GR/PR certification.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uY
variable {Y : Type uY} [MeasurableSpace Y]

/-- A frozen measurable finite-path observable with values in [0,1]. -/
structure FinitePathProperty (Y : Type uY) [MeasurableSpace Y] (L : ℕ) where
  score : ((i : Finset.Iic L) → Y) → ℝ
  measurable_score : Measurable score
  score_nonneg : ∀ w, 0 ≤ score w
  score_le_one : ∀ w, score w ≤ 1

namespace FinitePathProperty

/-- Bounded finite-prefix scores are integrable against any finite measure. -/
theorem integrable (L : ℕ) (f : FinitePathProperty Y L)
    (μ : Measure ((i : Finset.Iic L) → Y)) [IsFiniteMeasure μ] :
    Integrable f.score μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    f.measurable_score.aestronglyMeasurable (ae_of_all μ ?_)
  intro w
  rw [Real.norm_eq_abs, abs_of_nonneg (f.score_nonneg w)]
  exact f.score_le_one w

/-- Expected finite-prefix property under an arbitrary probability law. -/
noncomputable def expected (L : ℕ) (f : FinitePathProperty Y L)
    (μ : Measure ((i : Finset.Iic L) → Y)) : ℝ :=
  ∫ w, f.score w ∂μ

/-- Expected finite-prefix property under a point-started stationary kernel. -/
noncomputable def fromKernel (L : ℕ) (f : FinitePathProperty Y L)
    (K : Kernel Y Y) [IsMarkovKernel K] (y : Y) : ℝ :=
  f.expected L (PermanssonLean.ProbabilitySupport.finitePrefixLaw K y L)

end FinitePathProperty
end ConstitutiveQuasi
end PermanssonResearch
