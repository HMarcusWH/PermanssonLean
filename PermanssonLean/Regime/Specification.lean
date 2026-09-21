import Mathlib.MeasureTheory.Measure.Basic

open MeasureTheory

namespace PermanssonLean

universe uY uH

/--
Minimal ex-ante regime specification scaffold.

The paper freezes B₀ ⊆ B as Borel sets. We encode that measurability at the
specification boundary so persistence, killed-kernel, and occupation-law results do
not need to carry ad hoc measurable-set hypotheses downstream.

The full GR object will later add the limiting occupation law, convergence mode,
non-triviality gates, and persistence certificate exactly as frozen in v0.1.7.
-/
structure RegimeSpecification
    (Y : Type uY) (H : Type uH)
    [MeasurableSpace Y] [MeasurableSpace H] where
  region : Set Y
  region_measurable : MeasurableSet region
  basin : Set Y
  basin_measurable : MeasurableSet basin
  basin_subset_region : basin ⊆ region
  descriptor : Y → H
  descriptor_measurable : Measurable descriptor

end PermanssonLean
