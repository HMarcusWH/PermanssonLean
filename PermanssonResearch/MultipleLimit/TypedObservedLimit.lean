import PermanssonResearch.MultipleLimit.TypedRandomOccupation
import PermanssonResearch.MultipleLimit.DescriptorTransport
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Lane C1 — nonconstant observed limit despite a random physical terminal law

The full-state occupation limit is random (delta_a or delta_b). The
nonconstant ex-ante descriptor y ↦ y.1 maps both absorbing outcomes to
Bool.true, and by continuity of probability-measure pushforward the
observed empirical occupation has deterministic weak limit delta_true.

This does not collapse the two physical terminal laws or change the
frozen convergence mode.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedObservedLimit

open TypedStrategicWitness
open TypedRandomOccupation

theorem terminal_observed_law (w : ℕ → Y) :
    (terminalLaw (terminalDestination w)).map
      nonconstantAbsorptionDescriptor =
      diracProba true := by
  rw [terminalLaw_descriptor_apply]
  unfold terminalDestination
  split_ifs <;>
    rfl

theorem canonical_observed_weak_limit (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂model.pathLaw μ.toMeasure,
      Tendsto
        (fun n : ℕ =>
          (PermanssonLean.RegimeSpecification.empiricalOccupation
            PermanssonLean.PeriodicExactGR.spec w
            (n+1) (Nat.succ_pos n)).map nonconstantAbsorptionDescriptor)
        atTop (𝓝 (diracProba true)) := by
  filter_upwards [canonical_random_occupation_limit_unconditional μ] with w hw
  have hcontinuous : Continuous nonconstantAbsorptionDescriptor :=
    continuous_of_discreteTopology
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n : ℕ =>
      PermanssonLean.RegimeSpecification.empiricalOccupation
        PermanssonLean.PeriodicExactGR.spec w
        (n+1) (Nat.succ_pos n))
    (terminalLaw (terminalDestination w)) hw hcontinuous
  simpa only [terminal_observed_law w] using hmap

end TypedObservedLimit
end MultipleLimit
end PermanssonResearch
