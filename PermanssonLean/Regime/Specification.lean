import PermanssonLean.Regime.ConvergenceMode
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory

namespace PermanssonLean

universe uY uH

/--
Frozen ex-ante regime specification

\[
\Sigma=(B,B_0,h,\nu,\mathfrak c).
\]

The data boundary itself encodes the paper's Borel-set and measurability
requirements.  Chronological "declared before classification" semantics are
represented by passing this immutable object into the classifier; they are not
re-stated as a post-hoc proposition over already constructed values.
-/
structure RegimeSpecification
    (Y : Type uY) (H : Type uH)
    [MeasurableSpace Y] [MeasurableSpace H] where
  /-- Predeclared regime region \(B\). -/
  region : Set Y
  region_measurable : MeasurableSet region
  /-- Predeclared initial basin \(B_0\). -/
  basin : Set Y
  basin_measurable : MeasurableSet basin
  basin_subset_region : basin ⊆ region
  /-- Borel descriptor \(h:Y\to H\), defined on the whole state space. -/
  descriptor : Y → H
  descriptor_measurable : Measurable descriptor
  /-- Declared limiting descriptor occupation law \(\nu\). -/
  target : ProbabilityMeasure H
  /-- Frozen convergence mode \(\mathfrak c\). -/
  convergenceMode : ConvergenceMode Y H

end PermanssonLean
