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
  rw [← intervenedValue_eq_goodMass typedModel
    (researchActionFamily sixStateMatrix) intervention observedDescriptor
    (decode i)]
  exact intervenedProperty_zero i hi

end
end ExactSixStateC7Witness
end MultipleLimit
end PermanssonResearch
