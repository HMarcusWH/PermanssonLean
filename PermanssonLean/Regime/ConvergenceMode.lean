import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Topology.Basic

open Filter MeasureTheory
open scoped Topology

namespace PermanssonLean

universe uY uH

/-- A random empirical occupation-law process indexed by positive horizons.

The third argument certifies that the horizon is strictly positive, matching the
paper's definition \(\widehat\nu_T^h = T^{-1}\sum_{t<T}\delta_{h(Y_t)}\).
-/
abbrev OccupationProcess
    (Y : Type uY) (H : Type uH)
    [MeasurableSpace Y] [MeasurableSpace H] :=
  (w : ℕ → Y) → (T : ℕ) → 0 < T → ProbabilityMeasure H

/-- Frozen convergence semantics for an occupation-law process.

The paper allows several canonical convergence modes and also permits another
precisely declared mode fixed ex ante.  The formal kernel therefore stores the
mode extensionally as the proposition it imposes on the path law, occupation
process, and deterministic target probability law.
-/
structure ConvergenceMode
    (Y : Type uY) (H : Type uH)
    [MeasurableSpace Y] [MeasurableSpace H] where
  holds :
    Measure (ℕ → Y) →
    OccupationProcess Y H →
    ProbabilityMeasure H →
    Prop

namespace ConvergenceMode

/-- Canonical almost-sure weak convergence of the empirical occupation law.

The topology on `ProbabilityMeasure H` is mathlib's weak-convergence topology.
The positive horizon is represented as `n + 1` along `atTop`.
-/
noncomputable def almostSureWeak
    (Y : Type uY) (H : Type uH)
    [MeasurableSpace Y] [MeasurableSpace H]
    [TopologicalSpace H] [OpensMeasurableSpace H] :
    ConvergenceMode Y H where
  holds μ occ ν :=
    ∀ᵐ w ∂μ,
      Tendsto
        (fun n : ℕ => occ w (n + 1) (Nat.succ_pos n))
        atTop
        (𝓝 ν)

/-- A convenience constructor for an explicitly supplied ex-ante convergence
predicate. -/
def custom
    (Y : Type uY) (H : Type uH)
    [MeasurableSpace Y] [MeasurableSpace H]
    (p :
      Measure (ℕ → Y) →
      OccupationProcess Y H →
      ProbabilityMeasure H →
      Prop) :
    ConvergenceMode Y H :=
  ⟨p⟩

end ConvergenceMode

end PermanssonLean
