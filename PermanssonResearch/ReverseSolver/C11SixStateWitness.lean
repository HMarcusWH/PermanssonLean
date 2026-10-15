import PermanssonResearch.ReverseSolver.C11ObservedStationary
import PermanssonResearch.ReverseSolver.ExactSixStateC10Execution
import PermanssonResearch.MultipleLimit.ExactSixStateStationaryCoordinates
import Mathlib.Tactic

/-!
# C11-A — canonical actual six-state stationary witnesses

Reuses the frozen C10 matrices and the C4 ORIGINAL typed class laws,
not a newly invented six-state surrogate. Checks complete stationary
equations and Boolean stationary shares for both baseline recurrent
classes, plus the false singleton created by the original full member.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace ReverseSolver
namespace C11

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

open C10
open PermanssonResearch.MultipleLimit.ExactSixState
open PermanssonResearch.MultipleLimit.ExactSixStateCanonical
open PermanssonResearch.MultipleLimit.ExactSixStateClassLaws
open PermanssonResearch.MultipleLimit.ExactSixStateStationaryCoordinates
open PermanssonResearch.MultipleLimit.ExactSixStateObservedGR
open FiniteStrategicRealization

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

def sixClassA : ClassStationaryCandidate 6 where
  classStates := {2, 3}
  weights := piA

def sixClassB : ClassStationaryCandidate 6 where
  classStates := {4, 5}
  weights := piB

theorem sixClassA_checked :
    checkClassStationary sixStateMatrix sixClassA = true := by
  decide +kernel

theorem sixClassB_checked :
    checkClassStationary sixStateMatrix sixClassB = true := by
  decide +kernel

theorem sixClassA_share :
    trueShare sixClassA sixRaw.descriptor = 1 := by
  decide +kernel

theorem sixClassB_share :
    trueShare sixClassB sixRaw.descriptor = 1 := by
  decide +kernel

/-- C4's entire actual class-supported stationary measure is recovered,
not just an independently recomputed numerical example. -/
theorem sixClassA_eq_C4 :
    certifiedProbability sixStateMatrix sixClassA sixClassA_checked =
      PermanssonResearch.MultipleLimit.ExactSixStateClassLaws.πA := by
  calc
    certifiedProbability sixStateMatrix sixClassA sixClassA_checked =
        explicitPiA := by rfl
    _ = PermanssonResearch.MultipleLimit.ExactSixStateClassLaws.πA := piA_eq_explicit.symm

theorem sixClassB_eq_C4 :
    certifiedProbability sixStateMatrix sixClassB sixClassB_checked =
      PermanssonResearch.MultipleLimit.ExactSixStateClassLaws.πB := by
  calc
    certifiedProbability sixStateMatrix sixClassB sixClassB_checked =
        explicitPiB := by rfl
    _ = PermanssonResearch.MultipleLimit.ExactSixStateClassLaws.πB := piB_eq_explicit.symm

/-- Original full-disruption member: the newly introduced absorbing
state u=1 has actual long-run false observation. -/
def sixFullFalseClass : ClassStationaryCandidate 6 where
  classStates := {1}
  weights := fun x => if x = (1 : Fin 6) then 1 else 0

theorem sixFullFalseClass_checked :
    checkClassStationary (sixMenuMatrix (0 : Fin 6))
      sixFullFalseClass = true := by
  decide +kernel

theorem sixFullFalseClass_share :
    trueShare sixFullFalseClass sixRaw.descriptor = 0 := by
  decide +kernel

/-- The checked full-member stationary law is an actual intervened
alpha-only C2 stationary class probability, not a fake baseline model. -/
theorem sixFullFalseClass_typed :
    certifiedProbability (sixMenuMatrix (0 : Fin 6))
      sixFullFalseClass sixFullFalseClass_checked =
    PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw.stationaryForSet
      (rationalStrategicIntervention sixStateMatrix
        (sixMenuMatrix (0 : Fin 6))).intervention.apply.inducedKernel
      (decodedClass sixFullFalseClass.classStates) :=
  checked_stationary_eq_native sixStateMatrix
    (sixMenuMatrix (0 : Fin 6)) sixFullFalseClass
    sixFullFalseClass_checked

end C11
end ReverseSolver
end PermanssonResearch
