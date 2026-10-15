import PermanssonResearch.RegimeExit.CanonicalTailKernel
import Mathlib.Tactic

/-!
# Lane C-Exit C — first-exit tail indexing and mass sanity

This is the first indispensable specialization of the full stopped-path
restart theorem: test the future observation at tail index ZERO. The
general conditional law of future paths remains a separate obligation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace A] [MeasurableSpace H]

/-- The time-(n+1) endpoint extracted from the shifted infinite
future is exactly the very first state of that future. -/
theorem shifted_future_zero (n : ℕ)
    (w : ℕ → JointState S X) :
    pathTailShift (S := S) (X := X) (n+1) w 0 = w (n+1) := by
  rfl

/-- The first-exit event and the shifted future's time-zero observable
reduce to one first-exit destination event. No extra stochastic
independence assumption is used. -/
theorem firstExit_shift_zero_inter
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ)
    (D C : Set (JointState S X)) :
    firstExitAtDestination spec n D ∩
      (pathTailShift (S := S) (X := X) (n+1)) ⁻¹'
        {v : ℕ → JointState S X | v 0 ∈ C} =
      firstExitAtDestination spec n (D ∩ C) := by
  ext w
  simp only [firstExitAtDestination, pathTailShift, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff]
  tauto

/-- The first observable at the stopping-time restart matches the
PR66 exact killed/exit step measure. This is an actual probability
identity on the canonical full-path law, not a finite-matrix estimate. -/
theorem firstExit_shift_zero_probability
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ spec.region)
    (D C : Set (JointState S X))
    (hD : MeasurableSet D) (hC : MeasurableSet C) :
    N.pathLaw (Measure.dirac y)
      (firstExitAtDestination spec n D ∩
        (pathTailShift (S := S) (X := X) (n+1)) ⁻¹'
          {v : ℕ → JointState S X | v 0 ∈ C}) =
      firstExitStepMeasure N spec n y (D ∩ C) := by
  rw [firstExit_shift_zero_inter]
  simpa only [firstExitStepMass] using
    firstExitStep_eq_pathEvent N spec n hy (D ∩ C) (hD.inter hC)

end PermanssonResearch.RegimeExit
