import PermanssonResearch.MultipleLimit.CanonicalClassSelector
import Mathlib.Tactic

/-!
# Lane C2 — canonical recurrent selection weights and eventual-class identity

For a genuine finite Markov chain and ANY initial probability law, the
previously constructed measurable recurrent-class selector selects the
unique eventual recurrent class a.s. Its weights sum to one and obey
the genuine arbitrary-initial-state infinite-path mixture identity.

The weights describe CLASS SELECTION, not the not-yet-proved class
stationary distribution or almost-sure empirical occupation measure.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace CanonicalClassWeights

open KernelCommunication
open RecurrentClassDecomposition
open CanonicalClassSelector
open CanonicalClassEntry
open CanonicalClassContinuation
open CanonicalRecurrentResidence
open FiniteCanonicalPath

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- The selected class is the TRUE eventual recurrent class for
canonical-almost every infinite trajectory, not just an arbitrary
member of the finite class collection. -/
theorem selected_class_eventual_ae (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      EventuallyInClass w (CommunicatingClass K
        (selectedRepresentative K w)) := by
  filter_upwards [canonical_ae_enters_recurrent K μ,
    all_closed_classes_stay_ae K μ] with w hhit hstay
  have hh : HasRecurrentHit K w := hhit
  have hfirst : firstRecurrentState K w ∈ RecurrentStates K :=
    firstRecurrentState_mem K w hh
  let C := CommunicatingClass K (firstRecurrentState K w)
  have hclosed : ClosedSubset K C := hfirst
  have hmem : w (firstRecurrentIndex K w) ∈ C := by
    change firstRecurrentState K w ∈
      CommunicatingClass K (firstRecurrentState K w)
    exact mem_communicatingClass K _
  have hclass :
      CommunicatingClass K (selectedRepresentative K w) = C := by
    unfold selectedRepresentative
    rw [dif_pos hh]
    exact (communicatingClass_eq_of_communicates K
      (classRepresentative_mem K (firstRecurrentState K w))).symm
  refine ⟨firstRecurrentIndex K w, ?_⟩
  intro n hn
  rw [hclass]
  exact hstay C hclosed (firstRecurrentIndex K w) hmem n hn

/-- Unique eventual recurrence is independent of the selector's
arbitrary choice of the time-zero no-hit fallback on null paths. -/
theorem selected_class_identifies_unique_ae
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∀ C ∈ RecurrentClasses K,
        EventuallyInClass w C →
          C = CommunicatingClass K (selectedRepresentative K w) := by
  filter_upwards [selected_class_eventual_ae K μ] with w hw
  intro C hC hE
  have hsel :
      CommunicatingClass K (selectedRepresentative K w) ∈
        RecurrentClasses K :=
    (recurrentClasses_mem_iff K _).mpr
      ⟨selectedRepresentative K w,
        selectedRepresentative_recurrent K w, rfl⟩
  exact eventual_class_unique K w hC hsel hE hw

/-- Class-selection weights are an exact probability vector, because
the measurable canonical selector takes values in the certified finite
recurrent-representative set for EVERY path (including exceptional
zero-measure trajectories). -/
theorem class_selection_weights_sum_one
    (μ : ProbabilityMeasure Y) :
    (∑ i ∈ recurrentRepresentatives K,
      (canonicalPathLaw K μ.toMeasure)
        ((selectedRepresentative K) ⁻¹' {i})) = 1 := by
  classical
  let P := canonicalPathLaw K μ.toMeasure
  let f := selectedRepresentative K
  let s := recurrentRepresentatives K
  have hf : Measurable f := selectedRepresentative_measurable K
  have hpre : f ⁻¹' (↑s : Set Y) = Set.univ := by
    ext w
    simp [f, s, selectedRepresentative_mem K w]
  calc
    (∑ i ∈ s, P (f ⁻¹' ({i} : Set Y))) =
        P (f ⁻¹' (↑s : Set Y)) := by
      exact Measure.sum_measure_preimage_singleton s
        (fun i hi => (measurableSet_singleton i).preimage hf)
    _ = P Set.univ := by rw [hpre]
    _ = 1 := measure_univ

/-- The class-selection law depends AFFINELY on the initial
probability law. It is derived from the actual infinite canonical
path-law mixture and requires no assumed stationary distribution. -/
theorem class_selection_weight_initial_mixture
    (μ : ProbabilityMeasure Y) (i : Y) :
    (canonicalPathLaw K μ.toMeasure)
      ((selectedRepresentative K) ⁻¹' {i}) =
    ∑ y : Y, μ.toMeasure {y} *
      (canonicalPathLaw K (Measure.dirac y))
        ((selectedRepresentative K) ⁻¹' {i}) := by
  apply canonicalPathLaw_event_initial_mixture K μ
  exact (measurableSet_singleton i).preimage
    (selectedRepresentative_measurable K)

end CanonicalClassWeights
end MultipleLimit
end PermanssonResearch
