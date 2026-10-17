import PermanssonResearch.X1.TypedModels
import PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
import PermanssonResearch.MultipleLimit.FiniteExactGRRecovery
import PermanssonLean.Quotient.Compression

/-!
# X1: actual canonical random occupation limits

The existing finite-chain strong law applies directly to BOTH actual typed
models. No invariant law, initial stationarity, irreducibility, aperiodicity or
Exact-GR hypothesis is supplied. The limit is the stationary law of the
recurrent class selected by the actual infinite path; it may be random.

The separately recorded rational descriptor targets are NOT identified by
these theorems. Their deterministic identification still requires the exact
model/quotient/stationary-certificate bridge. A finite stationary receipt
alone does not discharge that obligation.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace PermanssonResearch.X1

set_option autoImplicit false

open PermanssonLean
open PermanssonResearch.MultipleLimit

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- Whole physical occupation limit of the actual model, indexed by its
genuine selected recurrent class, not a stationary barycenter. -/
noncomputable def physicalRandomLimit (m : Mode) (w : ℕ → Y) : ProbabilityMeasure Y :=
  FiniteOccupationRandomLaw.physicalOccupationLimit (model m).inducedKernel w

/-- Observed random limit for the PREDECLARED world descriptor. -/
noncomputable def observedRandomLimit (m : Mode) (w : ℕ → Y) : ProbabilityMeasure Bool :=
  FiniteOccupationRandomLaw.observedOccupationLimit (model m).inducedKernel descriptor w

theorem physicalRandomLimit_measurable (m : Mode) : Measurable (physicalRandomLimit m) :=
  FiniteOccupationRandomLaw.physicalOccupationLimit_measurable (model m).inducedKernel

theorem observedRandomLimit_measurable (m : Mode) : Measurable (observedRandomLimit m) :=
  FiniteOccupationRandomLaw.observedOccupationLimit_measurable (model m).inducedKernel descriptor

/-- Actual alpha/P/U infinite path law, arbitrary initial probability law,
and the genuine time-zero-inclusive physical empirical occupation sequence. -/
theorem physicalRandomLimit_ae (m : Mode) (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂(model m).pathLaw μ.toMeasure,
      Tendsto (fun n : ℕ =>
        FiniteStateOccupation.empiricalOccupation w (n+1) (Nat.succ_pos n))
        atTop (𝓝 (physicalRandomLimit m w)) := by
  rw [FiniteCanonicalPath.typed_pathLaw_eq_canonical]
  exact FiniteOccupationRandomLaw.physicalOccupationLimit_ae_correct
    (model m).inducedKernel μ

/-- Actual descriptor empirical occupations converge a.s. This rules out an
unsupported claim of persistent occupation nonconvergence for the learner. -/
theorem observedRandomLimit_ae (m : Mode) (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂(model m).pathLaw μ.toMeasure,
      Tendsto (fun n : ℕ =>
        (FiniteStateOccupation.empiricalOccupation w (n+1) (Nat.succ_pos n)).map descriptor)
        atTop (𝓝 (observedRandomLimit m w)) := by
  rw [FiniteCanonicalPath.typed_pathLaw_eq_canonical]
  exact FiniteOccupationRandomLaw.observedOccupationLimit_ae_correct
    (model m).inducedKernel μ descriptor

/-- The SAME a.s. limit for the ORIGINAL frozen empirical-occupation
definition whenever its descriptor is the registered X1 descriptor. This is
an occupation statement only; it requires neither and proves neither Exact GR
nor equality to the specification's separately recorded target. -/
theorem original_empirical_randomLimit_ae (m : Mode)
    (spec : RegimeSpecification Y Bool) (hdesc : spec.descriptor = descriptor)
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂(model m).pathLaw μ.toMeasure,
      Tendsto (fun n : ℕ =>
        RegimeSpecification.empiricalOccupation spec w (n+1) (Nat.succ_pos n))
        atTop (𝓝 (observedRandomLimit m w)) := by
  filter_upwards [observedRandomLimit_ae m μ] with w hw
  have hsequence :
      (fun n : ℕ =>
        RegimeSpecification.empiricalOccupation spec w (n+1) (Nat.succ_pos n)) =
      (fun n : ℕ =>
        (FiniteStateOccupation.empiricalOccupation w (n+1) (Nat.succ_pos n)).map descriptor) := by
    funext n
    rw [FiniteExactGRRecovery.original_empirical_eq_physical_map, hdesc]
  rw [hsequence]
  exact hw

/-- The WHOLE law on observed probability measures, with actual recurrent
class-selection weights under the actual typed infinite path measure. -/
theorem observedRandomLimit_full_law (m : Mode) (μ : ProbabilityMeasure Y) :
    ((model m).pathLaw μ.toMeasure).map (observedRandomLimit m) =
      ∑ i ∈ CanonicalClassSelector.recurrentRepresentatives (model m).inducedKernel,
        (model m).pathLaw μ.toMeasure
          ((CanonicalClassSelector.selectedRepresentative (model m).inducedKernel) ⁻¹' {i}) •
          Measure.dirac
            (ClassDescriptorSelectionLaw.observedStationaryForClass
              (model m).inducedKernel descriptor i) := by
  rw [FiniteCanonicalPath.typed_pathLaw_eq_canonical]
  exact FiniteOccupationRandomLaw.observedOccupationLimit_full_law
    (model m).inducedKernel μ descriptor

end PermanssonResearch.X1
