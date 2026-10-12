import PermanssonResearch.MultipleLimit.ExactSixStateConstitution
import PermanssonLean.Regime.GroundedPermansson
import Mathlib.Tactic

/-!
# C6 — groundedness of the SAME frozen descriptor event

The original Boolean descriptor alone cannot recover the full
proper regime region (t and u have the same observed value but one
is outside the region). We therefore freeze a relevance map containing
both region membership and the original descriptor:
  g(y) = (decide(y in original region), observedDescriptor y).
The event property factors globally through the second coordinate,
independently of which intervened process generated the path law.

The derived result is original grounded generalized PR, not the
confirmatory PR_g subclass without a separately certified confirmatory
baseline.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace GroundedC6Response

open PermanssonLean
open PermanssonLean.RegimeSpecification
open ExactSixStateTyped
open ExactSixStateObservedGR
open ExactSixStateTargetDisruption
open TypedEventResponse
open ExactSixStateConstitution
open FrozenObservedEvent

noncomputable section

abbrev SixY := JointState Unit (Fin 6)

/-- Frozen, non-post-hoc observation carries both region membership and
the exact original Boolean descriptor. The world kernel is NOT read by g. -/
noncomputable def relevance :
    GroundedRelevanceMap observedSpec (Bool × Bool) := by
  classical
  refine {
    observe := fun y : SixY =>
      (decide (y ∈ observedSpec.region), observedDescriptor y)
    observe_measurable := Measurable.of_discrete
    regimeRegion := {z : Bool × Bool | z.1 = true}
    regimeRegion_measurable := MeasurableSet.of_discrete
    region_preimage := ?_
    descriptor := Prod.snd
    descriptor_measurable := measurable_snd
    descriptor_factor := ?_ }
  · ext y
    simp
  · rfl

/-- The event on relevant paths depends on the second observed Boolean,
not on hidden physical labels or class selectors. -/
noncomputable def groundedProperty :
    RegimePropertyMap (Bool × Bool) ℝ :=
  eventuallyObservedProperty (fun z : Bool × Bool => z.2) true

/-- The original full-path event is the exact inverse image of the
frozen relevant-path event, for EVERY sample path, including null paths. -/
theorem frozen_event_factors :
    TypedEventResponse.eventuallyTrue =
      relevance.pathMap ⁻¹'
        eventuallyObserved (fun z : Bool × Bool => z.2) true := by
  ext w
  constructor
  · rintro ⟨N,hN⟩
    exact ⟨N, fun n hn => by
      change observedDescriptor (w n) = true
      exact hN n hn⟩
  · rintro ⟨N,hN⟩
    exact ⟨N, fun n hn => by
      have h := hN n hn
      change observedDescriptor (w n) = true at h
      exact h⟩

/-- Global factorization holds for arbitrary probability laws, not only
the baseline or intervened path law: no process-specific adjustment of ψ. -/
theorem property_factors_globally :
    GloballyFactorsThroughRelevanceMap observedSpec fixedProperty relevance := by
  refine ⟨groundedProperty, ?_⟩
  intro μ
  change (μ.toMeasure TypedEventResponse.eventuallyTrue).toReal =
    ((μ.map relevance.pathMap).toMeasure
      (eventuallyObserved (fun z : Bool × Bool => z.2) true)).toReal
  have hE := frozen_event_factors
  change (μ.toMeasure TypedEventResponse.eventuallyTrue).toReal =
    ((Measure.map relevance.pathMap μ.toMeasure)
      (eventuallyObserved (fun z : Bool × Bool => z.2) true)).toReal
  rw [Measure.map_apply relevance.pathMap_measurable
    (eventuallyObserved_measurable
      (fun z : Bool × Bool => z.2) true measurable_snd)]
  rw [← hE]

/-- The original baseline and intervened laws share exactly the SAME
grounded relevance-functional semantics. -/
theorem grounded_relative_property :
    IsGroundedPropertyRelative typedModel observedSpec
      (ReverseSolver.FiniteStrategicRealization.researchActionFamily
        ExactSixStateCanonical.sixStateMatrix)
      fixedProperty relevance intervention :=
  (property_factors_globally.relative
    typedModel observedSpec
    (ReverseSolver.FiniteStrategicRealization.researchActionFamily
      ExactSixStateCanonical.sixStateMatrix)
    fixedProperty relevance intervention)

/-- Strictly stronger original grounded-relative PR status, combining
the UNWEAKENED original quantitative C6 certificate with the same
globally grounded frozen path property. -/
theorem groundedRelativePR :
    IsGroundedPermanssonRegimeRelative
      typedModel observedSpec observedReference
      (ReverseSolver.FiniteStrategicRealization.researchActionFamily
        ExactSixStateCanonical.sixStateMatrix)
      fixedProperty relevance comparison intervention :=
  ⟨genuineRelativePR, grounded_relative_property⟩

end
end GroundedC6Response
end MultipleLimit
end PermanssonResearch
