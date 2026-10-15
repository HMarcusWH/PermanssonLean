import PermanssonResearch.RegimeExit.ExitFiniteWitness
import Mathlib.Tactic

/-!
# C-Exit — destination overlap is masked by the original frozen region

The routing operation is a measure on true FIRST-EXIT destinations, not
the arbitrary world target D as supplied. In particular, every inside-B
portion of D contributes zero, for finite and infinite first-exit events.
The final typed F1 check uses the actual alpha/P/U kernel.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit.ExitDestinationMask

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.RegimeExit
open PermanssonResearch.RegimeExit.ExitModels
open PermanssonResearch.RegimeExit.ExitFiniteWitness
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

theorem firstExitWithinDestination_mask
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (D : Set (JointState S X)) :
    firstExitWithinDestination spec L D =
      firstExitWithinDestination spec L (D \ spec.region) := by
  ext w
  simp only [firstExitWithinDestination, Set.mem_iUnion]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n, ?_⟩
    rw [← firstExitAtDestination_mask spec (n : ℕ) D]
    exact hn
  · rintro ⟨n,hn⟩
    refine ⟨n, ?_⟩
    rw [firstExitAtDestination_mask spec (n : ℕ) D]
    exact hn

theorem firstExitEverDestination_mask
    (spec : RegimeSpecification (JointState S X) H)
    (D : Set (JointState S X)) :
    firstExitEverDestination spec D =
      firstExitEverDestination spec (D \ spec.region) := by
  ext w
  simp only [firstExitEverDestination, Set.mem_iUnion]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n, ?_⟩
    rw [← firstExitAtDestination_mask spec n D]
    exact hn
  · rintro ⟨n,hn⟩
    refine ⟨n, ?_⟩
    rw [firstExitAtDestination_mask spec n D]
    exact hn

theorem exitRoutingFinite_mask
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    exitRoutingFinite M spec L y D =
      exitRoutingFinite M spec L y (D \ spec.region) := by
  rw [exitRouting_eq_prob_exit_in M spec L hy D hD,
    exitRouting_eq_prob_exit_in M spec L hy (D \ spec.region)
      (hD.diff spec.region_measurable)]
  exact congrArg (M.pathLaw (Measure.dirac y))
    (firstExitWithinDestination_mask spec L D)

theorem exitRoutingInfinite_mask
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    exitRoutingInfinite M spec y D =
      exitRoutingInfinite M spec y (D \ spec.region) := by
  rw [exitRoutingInfinite_eq_prob_exit_in M spec hy D hD,
    exitRoutingInfinite_eq_prob_exit_in M spec hy (D \ spec.region)
      (hD.diff spec.region_measurable)]
  exact congrArg (M.pathLaw (Measure.dirac y))
    (firstExitEverDestination_mask spec D)

/-- Actual model F1: a destination containing b and a has precisely the
same routing mass as the destination containing only outside state a. -/
theorem f1_typed_overlap_destination_at_one :
    exitRoutingFinite f1Model f1Spec 1 b
        (encode ⁻¹' ({0,1} : Set (Fin 3))) =
      exitRoutingFinite f1Model f1Spec 1 b destinationA := by
  have hb : b ∈ f1Spec.region := by
    simp [b, f1Spec, decode]
  have hD : MeasurableSet
      (encode ⁻¹' ({0,1} : Set (Fin 3))) :=
    MeasurableSet.of_discrete
  rw [exitRoutingFinite_mask f1Model f1Spec 1 hb
    (encode ⁻¹' ({0,1} : Set (Fin 3))) hD]
  have hOut :
      (encode ⁻¹' ({0,1} : Set (Fin 3))) \ f1Spec.region =
        destinationA := by
    ext y
    rcases y with ⟨u,x⟩
    cases u
    fin_cases x <;> simp [destinationA, encode, f1Spec]
  rw [hOut]

end PermanssonResearch.RegimeExit.ExitDestinationMask
