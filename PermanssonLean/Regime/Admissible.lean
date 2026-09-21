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
    (spec : RegimeSpecification Y H)
    (initLaw : ProbabilityMeasure Y) : Prop :=
  initLaw.toMeasure spec.basin = 1

theorem admissible_mass_region
    (spec : RegimeSpecification Y H)
    (initLaw : ProbabilityMeasure Y)
    (hinitLaw : IsAdmissibleInitialLaw spec initLaw) :
    initLaw.toMeasure spec.region = 1 := by
  apply le_antisymm (prob_le_one) ?_
  rw [← hinitLaw]
  exact measure_mono spec.basin_subset_region

theorem dirac_admissible_iff
    [MeasurableSingletonClass Y]
    (spec : RegimeSpecification Y H) (y : Y) :
    IsAdmissibleInitialLaw spec (diracProba y) ↔ y ∈ spec.basin := by
  unfold IsAdmissibleInitialLaw
  rw [diracProba_toMeasure_apply' y spec.basin_measurable]
  by_cases hy : y ∈ spec.basin <;> simp [hy]

end PermanssonLean
