import PermanssonResearch.MultipleLimit.FiniteClassInvariantMeasure
import PermanssonResearch.MultipleLimit.CanonicalClassWeights
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Lane C2 — measurable random stationary law indexed by the reached class

Using the unique actual stationary probability on EACH closed recurrent
class, assign a probability measure π_C to the uniquely selected class
of every infinite trajectory. The law of this MEASURE-VALUED random
variable is an exact finite weighted sum of Dirac measures at π_C,
with the genuine class-entry probabilities as weights.

This is NOT YET a law of empirical-occupation limits: proving that
μ̂_n converges to π_(selected class) almost surely requires a separate
true Markov martingale strong law. The distinction is mathematical,
not editorial.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace ClassStationarySelectionLaw

open KernelCommunication
open RecurrentClassDecomposition
open CanonicalClassSelector
open FiniteCanonicalPath
open FiniteClassInvariantMeasure

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- A total class-indexed stationary probability: for valid recurrent
classes use the unique proved invariant law; other sets get a
fixed harmless Dirac fallback without any certification claim. -/
noncomputable def stationaryForSet (C : Set Y) : ProbabilityMeasure Y := by
  classical
  exact if hC : C ∈ RecurrentClasses K then
    Classical.choose
      (exists_unique_stationary_probability_on_class K C hC)
  else MeasureTheory.diracProba (Classical.choice inferInstance)

/-- The valid-class branch is fully certified without any assumed
stationarity/uniqueness fields. -/
theorem stationaryForSet_spec {C : Set Y}
    (hC : C ∈ RecurrentClasses K) :
    Kernel.Invariant K (stationaryForSet K C).toMeasure ∧
      (stationaryForSet K C).toMeasure C = 1 := by
  classical
  unfold stationaryForSet
  rw [dif_pos hC]
  exact (Classical.choose_spec
    (exists_unique_stationary_probability_on_class K C hC)).1

/-- Stationarity and mass-one support of the class selected by the
actual canonical infinite trajectory; valid for ALL paths because
the total selected representative was assigned a recurrent fallback. -/
theorem selectedStationary_spec (w : ℕ → Y) :
    Kernel.Invariant K
      (stationaryForSet K (CommunicatingClass K
        (selectedRepresentative K w))).toMeasure ∧
    (stationaryForSet K (CommunicatingClass K
        (selectedRepresentative K w))).toMeasure
      (CommunicatingClass K (selectedRepresentative K w)) = 1 := by
  apply stationaryForSet_spec K
  exact (recurrentClasses_mem_iff K _).mpr
    ⟨selectedRepresentative K w,
      selectedRepresentative_recurrent K w, rfl⟩

/-- The assignment from physical recurrent representative to the
proved unique class stationary probability is measurable because
the physical state space is finite and singletons are measurable. -/
theorem classStationaryAssignment_measurable :
    Measurable (fun i : Y => stationaryForSet K
      (CommunicatingClass K i)) :=
  measurable_of_finite _

/-- Genuine full probability distribution ON PROBABILITY MEASURES
of the stationary law selected by the canonical path's recurrent
class. The weights use actual infinite-path probabilities.

This theorem does not identify the selected stationary law with
the almost-sure empirical occupation limit (that requires SLLN).
-/
theorem stationarySelection_full_law (μ : ProbabilityMeasure Y) :
    (canonicalPathLaw K μ.toMeasure).map
      (fun w => stationaryForSet K (CommunicatingClass K
        (selectedRepresentative K w))) =
      ∑ i ∈ recurrentRepresentatives K,
        (canonicalPathLaw K μ.toMeasure)
          ((selectedRepresentative K) ⁻¹' {i}) •
          Measure.dirac (stationaryForSet K (CommunicatingClass K i)) := by
  exact selectedRepresentative_transport K μ
    (fun i : Y => stationaryForSet K (CommunicatingClass K i))
    (classStationaryAssignment_measurable K)

end ClassStationarySelectionLaw
end MultipleLimit
end PermanssonResearch
