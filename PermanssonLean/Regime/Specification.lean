import Mathlib.MeasureTheory.Measure.Basic

open MeasureTheory

namespace PermanssonLean

universe uY uH

/--
Minimal ex-ante regime specification scaffold.

The full GR object will later add the limiting occupation law, convergence mode,
non-triviality gates, and persistence certificate exactly as frozen in v0.1.7.
-/
structure RegimeSpecification
    (Y : Type uY) (H : Type uH)
    [MeasurableSpace Y] [MeasurableSpace H] where
  region : Set Y
  basin : Set Y
  descriptor : Y → H
  descriptor_measurable : Measurable descriptor

end PermanssonLean
