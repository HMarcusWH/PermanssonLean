import PermanssonResearch.RegimeExit.ExitConservation
import PermanssonResearch.RegimeExit.QSDDestination
import Mathlib.Tactic

/-!
# C-Exit — remove the redundant QSD mass-conservation premise

For θ=1, the actual one-step exit mass under the QSD must be zero.
This follows from the ALREADY PROVED law-started finite routing mass
conservation and original QSD survival, not from an assumed conservation
field.  The theorem is law-relative: other states in B may still leak.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
open PermanssonLean PermanssonLean.RegimeSpecification

/-- The one-transition law-started routing measure is definitionally the
actual exit-subkernel integrated against the supplied initial law. -/
theorem qsdOneStepExitMass_eq_route_one
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (D : Set (JointState S X)) :
    qsdOneStepExitMass M spec μ D =
      exitRoutingFiniteFromLaw M spec 1 μ D := by
  change (exitSubkernel M spec ∘ₘ μ.toMeasure) D =
    ((0 : Measure (JointState S X)) +
      (exitSubkernel M spec ∘ₘ μ.toMeasure)) D
  simp

/-- The subkernel sends all its mass outside B; its law-integrated measure
agrees on the entire space and its outside part. -/
theorem qsdOneStepExitMass_outside_eq_univ
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X)) :
    qsdOneStepExitMass M spec μ (Set.univ \ spec.region) =
      qsdOneStepExitMass M spec μ Set.univ := by
  unfold qsdOneStepExitMass
  rw [Measure.bind_apply (MeasurableSet.univ.diff spec.region_measurable)
      (Kernel.aemeasurable _)]
  rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
  congr 1
  funext z
  exact (exitSubkernel_mask M spec z
    (D := Set.univ) MeasurableSet.univ).symm

/-- θ=1 QSDs have zero exit mass from their OWN initial distribution,
without extra conservation assumptions. No all-state assertion follows. -/
theorem qsdThetaOne_no_exit
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (hQ : IsQuasiStationaryDistribution M spec μ 1)
    (D : Set (JointState S X))
    (hD : MeasurableSet D) :
    qsdOneStepExitMass M spec μ D = 0 := by
  have hSupport : μ.toMeasure spec.region = 1 :=
    qsd_supported M spec μ 1 hQ
  have hsurvival : survivalProbabilityFromLaw M spec μ 1 = 1 := by
    simpa using (qsd_survivalProbability M spec μ 1 hQ 1)
  have hRouteConservation :=
    exitRoutingFromLaw_add_survival_eq_one M spec 1 μ hSupport
  rw [← qsdOneStepExitMass_eq_route_one M spec μ
      (Set.univ \ spec.region),
    qsdOneStepExitMass_outside_eq_univ M spec μ,
    hsurvival] at hRouteConservation
  have hstay : (killedKernel M spec ∘ₘ μ.toMeasure) Set.univ = 1 := by
    rw [qsd_eigenmeasure M spec μ 1 hQ]
    simp
  have hMassConservation :
      qsdOneStepExitMass M spec μ Set.univ +
        (killedKernel M spec ∘ₘ μ.toMeasure) Set.univ = 1 := by
    simpa only [hstay] using hRouteConservation
  exact qsdThetaOne_no_exit_of_conservation M spec μ hQ D hD
    hMassConservation

end PermanssonResearch.RegimeExit
