import PermanssonResearch.MultipleLimit.TypedAlmostSureAbsorption
import PermanssonResearch.MultipleLimit.MeasurableDestination
import Mathlib.Tactic

/-!
# Lane C1 — unconditional almost-sure weak random occupation limit

The existing frozen empirical occupation measure and its weak topology
are kept intact. The previously certified conditional Cesaro theorem
is instantiated by the actual typed model's almost-sure absorption,
rather than assuming h_abs as an external premise.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedRandomOccupation

open TypedStrategicWitness TypedAlmostSureAbsorption
open PermanssonLean.RegimeSpecification

/-- The literal alpha/P/U witness has an almost-sure weak limit equal to
the Dirac probability measure of its random eventual absorbing state. -/
theorem canonical_random_occupation_limit_unconditional
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂model.pathLaw μ.toMeasure,
      Tendsto
        (fun n : ℕ => empiricalOccupation PermanssonLean.PeriodicExactGR.spec w
          (n+1) (Nat.succ_pos n))
        atTop (𝓝 (terminalLaw (terminalDestination w))) := by
  apply canonical_random_occupation_limit model μ
  have h := canonical_eventual_a_or_b μ
  simpa only [TypedStrategicWitness.a, TypedStrategicWitness.b,
    absorbingA, absorbingB] using h

end TypedRandomOccupation
end MultipleLimit
end PermanssonResearch
