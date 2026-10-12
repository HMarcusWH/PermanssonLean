import PermanssonResearch.MultipleLimit.CanonicalClassWeights
import PermanssonResearch.MultipleLimit.ClassDescriptorSelectionLaw
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.Tactic

/-!
# Lane C2 — ex-ante basin and genuinely reachable recurrent-class family

The original single-target RegimeSpecification is NOT changed.
This separate research object freezes a basin and a proper regime region,
requires a nonempty basin and genuine one-step region closure, and
computes the class family only from positive probability of selecting a
recurrent class under genuine point-started canonical path laws.

A large post-hoc superset of possible outcomes is never a certificate
from this definition. No occupation convergence or constitutive PR status
is claimed here: those require separate theorems.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace BasinFamily

open KernelCommunication
open RecurrentClassDecomposition
open CanonicalClassSelector
open CanonicalClassWeights
open FiniteCanonicalPath

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]
variable (H : Type*) [MeasurableSpace H]

/-- New, independently frozen multiple-limit candidate data.
The region must be exactly closed for the declared kernel; this is a
separate gate from random occupation convergence. -/
structure FrozenBasinFamily where
  region : Set Y
  basin : Set Y
  basin_nonempty : basin.Nonempty
  basin_subset_region : basin ⊆ region
  region_closed : ClosedSubset K region
  descriptor : Y → H
  descriptor_measurable : Measurable descriptor

/-- The only admitted class representatives are those reached with
nonzero probability from at least one point of the frozen basin. -/
noncomputable def reachableRepresentatives
    (F : FrozenBasinFamily K H) : Finset Y := by
  classical
  exact (recurrentRepresentatives K).filter
    (fun i => ∃ y ∈ F.basin,
      canonicalPathLaw K (Measure.dirac y)
        ((selectedRepresentative K) ⁻¹' {i}) ≠ 0)

/-- Every selected representative lies in the registered recurrent
collection, even if the basin is restricted. -/
theorem reachable_subset_recurrent
    (F : FrozenBasinFamily K H)
    (i : Y) (hi : i ∈ reachableRepresentatives K H F) :
    i ∈ recurrentRepresentatives K := by
  classical
  exact (Finset.mem_filter.mp hi).1

/-- Excluded classes genuinely have zero entry probability from
every admitted point start. This is stronger than being absent from a
sampled trajectory, and excludes post-hoc padding by unreachable classes. -/
theorem unreachable_probability_zero
    (F : FrozenBasinFamily K H)
    (y : Y) (hy : y ∈ F.basin)
    (i : Y) (hi : i ∈ recurrentRepresentatives K)
    (hnot : i ∉ reachableRepresentatives K H F) :
    canonicalPathLaw K (Measure.dirac y)
      ((selectedRepresentative K) ⁻¹' {i}) = 0 := by
  classical
  by_contra hn
  apply hnot
  exact Finset.mem_filter.mpr ⟨hi, y, hy, hn⟩

/-- A nonempty frozen basin has a genuinely possible recurrent destination.
This is proved from the normalized canonical class-selection weights, not
from an arbitrary declared family member. -/
theorem reachableRepresentatives_nonempty
    (F : FrozenBasinFamily K H) :
    (reachableRepresentatives K H F).Nonempty := by
  classical
  obtain ⟨y, hy⟩ := F.basin_nonempty
  by_contra hn
  have hallzero (i : Y) (hi : i ∈ recurrentRepresentatives K) :
      canonicalPathLaw K (Measure.dirac y)
        ((selectedRepresentative K) ⁻¹' {i}) = 0 := by
    by_contra hne
    apply hn
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, y, hy, hne⟩⟩
  have hsum0 :
      (∑ i ∈ recurrentRepresentatives K,
        canonicalPathLaw K (Measure.dirac y)
          ((selectedRepresentative K) ⁻¹' {i})) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hallzero i hi
  have hsum1 := class_selection_weights_sum_one K (diracProba y)
  change (∑ i ∈ recurrentRepresentatives K,
      canonicalPathLaw K (Measure.dirac y)
        ((selectedRepresentative K) ⁻¹' {i})) = 1 at hsum1
  exact (zero_ne_one : (0 : ℝ≥0∞) ≠ 1) (hsum0.symm.trans hsum1)

end BasinFamily
end MultipleLimit
end PermanssonResearch
