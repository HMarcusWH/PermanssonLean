import PermanssonResearch.MultipleLimit.FiniteStateOccupation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Lane C2 — continuous pushforward of empirical occupation limits

When genuine empirical physical occupation measures converge weakly,
the observed occupation measures converge to the frozen descriptor
pushforward. On the finite discrete physical state space, EVERY frozen
descriptor is continuous, including a many-to-one descriptor that
identifies distinct recurrent classes.

This is a conditional topology/semantic bridge only. It does not assume
or prove the finite Markov strong law that supplies physical convergence.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace ClassDescriptorOccupationBridge

variable {Y H : Type*}
variable [MeasurableSpace Y] [MeasurableSpace H]
variable [TopologicalSpace Y] [TopologicalSpace H]

theorem descriptor_weak_limit_of_physical
    (h : Y → H) (hh : Continuous h)
    (w : ℕ → Y) (π : ProbabilityMeasure Y)
    (hphysical : Tendsto
      (fun n : ℕ =>
        FiniteStateOccupation.empiricalOccupation w (n+1)
          (Nat.succ_pos n))
      atTop (𝓝 π)) :
    Tendsto
      (fun n : ℕ =>
        (FiniteStateOccupation.empiricalOccupation w (n+1)
          (Nat.succ_pos n)).map h)
      atTop (𝓝 (π.map h)) := by
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n : ℕ =>
      FiniteStateOccupation.empiricalOccupation w (n+1) (Nat.succ_pos n))
    π hphysical hh

/-- No injectivity of h is required. Distinct recurrent classes may
have the same observed stationary-law pushforward, and both remain
covered by this exact continuous mapping theorem. -/
theorem finite_discrete_descriptor_limit
    [DiscreteTopology Y]
    (h : Y → H) (w : ℕ → Y) (π : ProbabilityMeasure Y)
    (hphysical : Tendsto
      (fun n : ℕ =>
        FiniteStateOccupation.empiricalOccupation w (n+1)
          (Nat.succ_pos n))
      atTop (𝓝 π)) :
    Tendsto
      (fun n : ℕ =>
        (FiniteStateOccupation.empiricalOccupation w (n+1)
          (Nat.succ_pos n)).map h)
      atTop (𝓝 (π.map h)) := by
  exact descriptor_weak_limit_of_physical h
    continuous_of_discreteTopology w π hphysical

end ClassDescriptorOccupationBridge
end MultipleLimit
end PermanssonResearch
