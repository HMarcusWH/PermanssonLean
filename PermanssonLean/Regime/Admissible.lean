import PermanssonLean.Regime.Specification
import Mathlib.MeasureTheory.Measure.DiracProba

open MeasureTheory

namespace PermanssonLean

universe uY uH

variable {Y : Type uY} {H : Type uH}
variable [MeasurableSpace Y] [MeasurableSpace H]

/-- The admissible initial-law class \(\mathcal D(B_0)\): probability laws
placing unit mass on the frozen basin. -/
def IsAdmissibleInitialLaw
    (Σ : RegimeSpecification Y H)
    (λ : ProbabilityMeasure Y) : Prop :=
  λ.toMeasure Σ.basin = 1

theorem admissible_mass_region
    (Σ : RegimeSpecification Y H)
    (λ : ProbabilityMeasure Y)
    (hλ : IsAdmissibleInitialLaw Σ λ) :
    λ.toMeasure Σ.region = 1 := by
  apply le_antisymm (prob_le_one) ?_
  rw [← hλ]
  exact measure_mono Σ.basin_subset_region

theorem dirac_admissible_iff
    [MeasurableSingletonClass Y]
    (Σ : RegimeSpecification Y H) (y : Y) :
    IsAdmissibleInitialLaw Σ (diracProba y) ↔ y ∈ Σ.basin := by
  simp [IsAdmissibleInitialLaw, diracProba, Σ.basin_measurable]

end PermanssonLean
