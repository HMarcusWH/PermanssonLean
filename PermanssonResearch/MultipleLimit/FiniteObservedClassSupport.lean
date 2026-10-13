import PermanssonResearch.MultipleLimit.FiniteOccupationStrongLaw
import PermanssonResearch.MultipleLimit.FiniteClassInvariantMeasure
import PermanssonResearch.MultipleLimit.CanonicalClassWeights
import Mathlib.Tactic

/-!
# C7-01 — strictly supported finite recurrent-class observations

For a genuine finite homogeneous Markov kernel, every member of a
closed communicating class has strictly positive mass under that class's
actual stationary probability. The all-true predicate is frozen from
a Boolean observation and the *current* kernel, never from a copied
baseline selector.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteObservedClassSupport

open KernelCommunication
open RecurrentClassDecomposition
open CanonicalClassSelector
open ClassStationarySelectionLaw
open FiniteClassInvariantMeasure
open FiniteClassInvariantUniqueness
open FiniteKernelRealBridge
open FiniteInvariantMeasureTransport
open FiniteKernelInvariantUniqueness

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- All members, not merely a full-measure subset, of the selected
irreducible class carry the declared Boolean label. -/
def AllTrueClass (h : Y → Bool) (i : Y) : Prop :=
  ∀ z ∈ CommunicatingClass K i, h z = true

/-- Good representatives are computed from K's OWN recurrent
decomposition, including when K was obtained by a typed intervention. -/
noncomputable def goodRecurrentRepresentatives (h : Y → Bool) : Finset Y := by
  classical
  exact (recurrentRepresentatives K).filter (AllTrueClass K h)

/-- The actual class-stationary probability has positive atom mass at
EVERY class member, including in a periodic recurrent class. -/
theorem stationary_point_positive
    (i z : Y) (hi : i ∈ RecurrentStates K)
    (hz : z ∈ CommunicatingClass K i) :
    0 < realPointMass
      (stationaryForSet K (CommunicatingClass K i)) z := by
  have hC : CommunicatingClass K i ∈ RecurrentClasses K :=
    (recurrentClasses_mem_iff K _).mpr ⟨i, hi, rfl⟩
  have hstat := stationaryForSet_spec K hC
  let π := stationaryForSet K (CommunicatingClass K i)
  exact strictly_positive_on_class
    (realTransition K) (realTransition_nonneg K)
    (CommunicatingClass K i) (class_real_irreducible K i)
    (realPointMass π) (realPointMass_nonneg π)
    (realPointMass_total π)
    (realPointMass_stationary K π hstat.1)
    (realPointMass_supported_of_class π _ hstat.2) z hz

end FiniteObservedClassSupport
end MultipleLimit
end PermanssonResearch
