import PermanssonResearch.MultipleLimit.FiniteObservedClassSupport
import PermanssonResearch.MultipleLimit.FrozenObservedEvent
import PermanssonResearch.MultipleLimit.FiniteOccupationOutside
import Mathlib.Tactic

/-!
# C7-02 — finite eventual-observation mass, from genuine infinite paths

The event "the frozen Boolean descriptor is eventually always true" is
almost surely equivalent to selection of a recurrent class on which ALL
states are labelled true. This is not a pointwise equivalence for
exceptional trajectories, nor a theorem about arbitrary weak-limit
events. It implies the exact sum of positive class-selection weights
without rational or aperiodicity assumptions.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteObservedEventMass

-- A misspelled or unresolved declaration must never become an implicit theorem premise.
set_option autoImplicit false

open KernelCommunication
open CanonicalClassSelector
open CanonicalClassWeights
open CanonicalRecurrentResidence
open FiniteCanonicalPath
open FiniteOccupationStrongLaw
open FiniteOccupationVector
open FiniteOccupationOutside
open FiniteKernelRealBridge
open FiniteKernelInvariantUniqueness
open FiniteInvariantMeasureTransport
open FiniteObservedClassSupport
open FrozenObservedEvent
open ClassStationarySelectionLaw

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable [DecidableEq Y] [StandardBorelSpace Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- The only nontrivial direction invokes the ALREADY PROVED all-chain
martingale occupation SLLN and positive stationary mass at every state
of the actually selected class. An arbitrary exceptional sequence may
have observed occupation delta_true but fail eventual constancy. -/
theorem eventuallyObserved_iff_selectedGood_ae
    (h : Y → Bool) (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      (w ∈ eventuallyObserved h true ↔
        AllTrueClass K h (selectedRepresentative K w)) := by
  filter_upwards [selected_class_eventual_ae K μ,
    canonical_empirical_vector_ae_limit K μ] with w hclass hvector
  constructor
  · intro hevent z hz
    by_contra hbad
    have hzero : Tendsto (fun n : ℕ => empiricalVector w n z)
        atTop (𝓝 (0 : ℝ)) := by
      apply empiricalVector_tendsto_zero_of_eventuallyInClass
        w {q : Y | h q = true} hevent z
      exact hbad
    have hstat : Tendsto (fun n : ℕ => empiricalVector w n z)
        atTop (𝓝 (realPointMass
          (stationaryForSet K (CommunicatingClass K
            (selectedRepresentative K w))) z)) :=
      (tendsto_pi_nhds.mp hvector) z
    have hval :
        realPointMass
          (stationaryForSet K (CommunicatingClass K
            (selectedRepresentative K w))) z = 0 :=
      tendsto_nhds_unique hstat hzero
    have hpositive := stationary_point_positive K
      (selectedRepresentative K w) z
      (selectedRepresentative_recurrent K w) hz
    exact (ne_of_gt hpositive) hval
  · intro hgood
    obtain ⟨N, hN⟩ := hclass
    exact ⟨N, fun n hn => hgood (w n) (hN n hn)⟩

/-- The event has exact ENNReal mass equal to the actual sum of the
good-class probabilities; the class selector and good set are both
taken from K, without a baseline-to-intervention class transport. -/
theorem eventuallyObserved_probability_eq_good_sum
    (h : Y → Bool) (μ : ProbabilityMeasure Y) :
    (canonicalPathLaw K μ.toMeasure)
      (eventuallyObserved h true) =
    ∑ i ∈ goodRecurrentRepresentatives K h,
      (canonicalPathLaw K μ.toMeasure)
        ((selectedRepresentative K) ⁻¹' ({i} : Set Y)) := by
  classical
  let P := canonicalPathLaw K μ.toMeasure
  let S := goodRecurrentRepresentatives K h
  have hevents :
      eventuallyObserved h true =ᵐ[P]
        ((selectedRepresentative K) ⁻¹' (↑S : Set Y)) := by
    filter_upwards [eventuallyObserved_iff_selectedGood_ae K h μ]
      with w hw
    change (w ∈ eventuallyObserved h true) ↔
      selectedRepresentative K w ∈ (↑S : Set Y)
    simpa only [S, goodRecurrentRepresentatives,
      Finset.mem_filter, selectedRepresentative_mem K w,
      true_and] using hw
  calc
    P (eventuallyObserved h true) =
        P ((selectedRepresentative K) ⁻¹' (↑S : Set Y)) :=
      measure_congr hevents
    _ = ∑ i ∈ S,
          P ((selectedRepresentative K) ⁻¹' ({i} : Set Y)) := by
      exact (sum_measure_preimage_singleton
        (μ := P) S
        (fun i hi => (measurableSet_singleton i).preimage
          (selectedRepresentative_measurable K))).symm

end FiniteObservedEventMass
end MultipleLimit
end PermanssonResearch
