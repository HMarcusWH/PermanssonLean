import PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Lane C2 — descriptor pushforward of selected recurrent-class stationary laws

For a frozen measurable descriptor h, each proven recurrent class invariant
probability has a canonical descriptor pushforward. The *entire law* of the
randomly selected descriptor measure is exactly a finite weighted Dirac sum.
Coincident observed class laws therefore aggregate their weights.

This is not yet a theorem that empirical occupation converges: the latter
requires the separate canonical finite-chain martingale strong law.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace ClassDescriptorSelectionLaw

open FiniteCanonicalPath
open KernelCommunication
open CanonicalClassSelector
open ClassStationarySelectionLaw

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]
variable {H : Type*} [MeasurableSpace H]

/-- The observed stationary law at a physical recurrent-class representative.
The observation h is frozen; no post-hoc regrouping changes it. -/
noncomputable def observedStationaryForClass (h : Y → H) (i : Y) :
    ProbabilityMeasure H :=
  (stationaryForSet K (CommunicatingClass K i)).map h

theorem observedStationaryAssignment_measurable (h : Y → H) :
    Measurable (fun i : Y => observedStationaryForClass K h i) :=
  measurable_of_finite _

/-- Exact complete distribution on probability measures of the observed
stationary law indexed by the actual canonical path's selected class.
This is a class-SELECTION law, not an assumed occupation limit. -/
theorem selected_observed_stationary_full_law
    (μ : ProbabilityMeasure Y) (h : Y → H) :
    (canonicalPathLaw K μ.toMeasure).map
        (fun w => observedStationaryForClass K h
          (selectedRepresentative K w)) =
      ∑ i ∈ recurrentRepresentatives K,
        (canonicalPathLaw K μ.toMeasure)
          ((selectedRepresentative K) ⁻¹' {i}) •
          Measure.dirac (observedStationaryForClass K h i) := by
  exact selectedRepresentative_transport K μ
    (fun i => observedStationaryForClass K h i)
    (observedStationaryAssignment_measurable K h)

/-- Two physical recurrent classes can have the SAME observed stationary
law. In that case their two atoms of the measure-valued output law
collapse, and their probabilities add, without assuming equal physical
class laws. -/
theorem combine_equal_observed_atoms (h : Y → H)
    (i j : Y)
    (hij : observedStationaryForClass K h i =
        observedStationaryForClass K h j)
    (a b : ℝ≥0∞) :
    a • Measure.dirac (observedStationaryForClass K h i) +
      b • Measure.dirac (observedStationaryForClass K h j) =
      (a+b) • Measure.dirac (observedStationaryForClass K h i) := by
  rw [← hij]
  exact (add_smul a b _).symm

end ClassDescriptorSelectionLaw
end MultipleLimit
end PermanssonResearch
