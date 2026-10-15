import PermanssonResearch.RegimeExit.SwitchRetentionMass
import PermanssonResearch.RegimeExit.ExitDiracBridge
import Mathlib.Tactic

/-!
# C-Exit B — actual finite-stopping arrival endpoint law

A finite first-exit endpoint measure is exactly PR66's killed/exit
step measure. No conditional restart of the infinite future is claimed
here; subsequent transitions and occupation limits remain separate.
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

/-- The arrival endpoint of all paths first exiting after n+1
transitions is a genuine measure on next-world states. It loses mass
on paths not exiting at that exact step. -/
noncomputable def firstExitArrivalEndpointMeasure
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X) :
    Measure (JointState S X) :=
  ((M.pathLaw (Measure.dirac y)).restrict
    (firstExitAtDestination spec n Set.univ)).map
      (fun w : ℕ → JointState S X => w (n+1))

/-- The PR66 first-exit step measure is the exact first-exit endpoint
measure of the ACTUAL canonical full-path law. The inside-B restriction
must not be replaced by a time-zero exit. -/
theorem firstExitArrivalEndpointMeasure_eq_step
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ spec.region) :
    firstExitArrivalEndpointMeasure M spec n y =
      firstExitStepMeasure M spec n y := by
  let P := M.pathLaw (Measure.dirac y)
  let endpoint : (ℕ → JointState S X) → JointState S X :=
    fun w => w (n+1)
  have hEvent (D : Set (JointState S X)) :
      endpoint ⁻¹' D ∩ firstExitAtDestination spec n Set.univ =
        firstExitAtDestination spec n D := by
    ext w
    constructor
    · rintro ⟨hD, hThrough, hExit⟩
      exact ⟨hThrough, hD, hExit.2⟩
    · rintro ⟨hThrough, hD, hOutside⟩
      exact ⟨hD, hThrough, ⟨Set.mem_univ _, hOutside⟩⟩
  ext D hD
  change ((P.restrict (firstExitAtDestination spec n Set.univ)).map
      endpoint) D = (firstExitStepMeasure M spec n y) D
  rw [Measure.map_apply (measurable_pi_apply (n+1)) hD,
    Measure.restrict_apply (hD.preimage (measurable_pi_apply (n+1))),
    hEvent D]
  exact (firstExitStep_eq_pathEvent M spec n hy D hD).symm

end PermanssonResearch.RegimeExit
