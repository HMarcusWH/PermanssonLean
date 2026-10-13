import PermanssonResearch.MultipleLimit.FiniteObservedUniformMargin
import PermanssonResearch.MultipleLimit.ExactSixStateConstitution
import PermanssonResearch.MultipleLimit.TypedEventResponse
import Mathlib.Tactic

/-!
# C7-05 — genuine C6 recovery through generic class-weight semantics

These are actual six-state alpha/P/U model kernels, not invented
reference matrices or transported baseline recurrent representatives.
The mixed periodic negative controls live in the independent exact
rational regression and are not promoted to original Exact GR status.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateC7Witness

-- A misspelled or unresolved declaration must never become an implicit theorem premise.
set_option autoImplicit false

open PermanssonLean
open PermanssonLean.RegimeSpecification
open ReverseSolver.FiniteStrategicRealization
open FiniteObservedUniformMargin
open TypedObservedEventConstitution
open FrozenObservedEvent
open ExactSixStateTyped
open ExactSixStateObservedGR
open ExactSixStateTargetDisruption
open ExactSixStateConstitution
open TypedEventResponse
open ExactSixStateCanonical
open ExactSixStateRecurrentGeometry
open KernelCommunication

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

abbrev SixY := JointState Unit (Fin 6)

/-- The GENERAL finite response theorem recovers C6's original
unweakened relative uniform PR for exactly the frozen descriptor. -/
theorem original_uniformPR_iff_exact_class_response :
    IsUniformGeneralizedPermanssonRegimeRelative
      typedModel observedSpec observedReference
      (researchActionFamily sixStateMatrix)
      (eventuallyObservedProperty observedDescriptor true)
      comparison intervention ↔
    IsExactGeneratedRegime typedModel observedSpec observedReference ∧
      ∀ y ∈ comparison.states,
        (pointGoodMass typedModel.inducedKernel observedDescriptor y).toReal ≠
        (pointGoodMass intervention.intervention.apply.inducedKernel
          observedDescriptor y).toReal :=
  uniformRelativePR_iff_finite_event_response
    typedModel observedSpec observedReference
    (researchActionFamily sixStateMatrix) comparison intervention

/-- Independent original C6 theorem passed through the general iff:
the actual class-weight response differs at every original basin point. -/
theorem c6_positive_response_everywhere :
    ∀ y ∈ comparison.states,
      (pointGoodMass typedModel.inducedKernel observedDescriptor y).toReal ≠
      (pointGoodMass intervention.intervention.apply.inducedKernel
        observedDescriptor y).toReal :=
  (original_uniformPR_iff_exact_class_response.mp
    (by simpa only [TypedEventResponse.fixedProperty] using uniformRelativePR)).2

/-- An actual point-started baseline six-state infinite-path event,
represented now by a generic sum over its genuine recurrent classes. -/
theorem baseline_good_mass_one (y : SixY) :
    (pointGoodMass typedModel.inducedKernel observedDescriptor y).toReal = 1 := by
  rw [← baselineValue_eq_goodMass typedModel observedDescriptor y]
  exact baselineProperty_one y

/-- The intervened model's OWN recurrent-class sum is zero from
each of the two original basin starts. -/
theorem intervened_good_mass_zero (i : Fin 6)
    (hi : i = 1 ∨ i = 2) :
    (pointGoodMass intervention.intervention.apply.inducedKernel
      observedDescriptor (decode i)).toReal = 0 := by
  calc
    (pointGoodMass intervention.intervention.apply.inducedKernel
      observedDescriptor (decode i)).toReal =
        intervenedPropertyValue
          (eventuallyObservedProperty observedDescriptor true)
          intervention.intervention (decode i) := by
            exact (intervenedValue_eq_goodMass
              typedModel (researchActionFamily sixStateMatrix)
              intervention observedDescriptor (decode i)).symm
    _ = 0 := by
      simpa only [TypedEventResponse.fixedProperty] using
        (intervenedProperty_zero i hi)


/-- Frozen alternate observation distinguishes the two genuine states
in the closed period-two A class; a mixed class is not an all-true
class, even though its empirical occupation converges. This formal
negative witness is NOT asserted to define a baseline Exact GR. -/
def mixedDescriptor (y : SixY) : Bool :=
  if encode y = (3 : Fin 6) then false else observedDescriptor y

/-- Both directions of the period-two communication are proved from
the ACTUAL induced typed kernel's exact singleton probabilities. -/
theorem mixed_periodic_A_not_good :
    ¬ FiniteObservedClassSupport.AllTrueClass
      typedModel.inducedKernel mixedDescriptor (decode (2 : Fin 6)) := by
  intro hgood
  have h23 : PositiveEdge typedModel.inducedKernel
      (decode (2 : Fin 6)) (decode (3 : Fin 6)) := by
    unfold PositiveEdge
    rw [typed_six_state_atom]
    norm_num [ExactSixState.transition]
  have h32 : PositiveEdge typedModel.inducedKernel
      (decode (3 : Fin 6)) (decode (2 : Fin 6)) := by
    unfold PositiveEdge
    rw [typed_six_state_atom]
    norm_num [ExactSixState.transition]
  have hmember :
      decode (3 : Fin 6) ∈
        CommunicatingClass typedModel.inducedKernel (decode (2 : Fin 6)) :=
    ⟨reachable_single typedModel.inducedKernel h23,
     reachable_single typedModel.inducedKernel h32⟩
  have hh := hgood (decode (3 : Fin 6)) hmember
  simp [mixedDescriptor, encode, decode] at hh

end
end ExactSixStateC7Witness
end MultipleLimit
end PermanssonResearch
