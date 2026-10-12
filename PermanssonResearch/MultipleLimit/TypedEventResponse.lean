import PermanssonResearch.MultipleLimit.ExactSixStateTargetDisruption
import PermanssonResearch.MultipleLimit.FiniteEventuallyObserved
import PermanssonLean.Regime.UniformPermansson
import Mathlib.Tactic

/-!
# C6 — one frozen descriptor event evaluated on two typed infinite laws

The path predicate is declared exclusively from the original Boolean
regime descriptor. Both the baseline and the typed intervention evaluate
THE SAME RegimePropertyMap on their genuine infinite alpha/P/U laws.
No baseline-specific class selector is reused after intervention.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedEventResponse

open PermanssonLean
open PermanssonLean.RegimeSpecification
open ReverseSolver.FiniteStrategicRealization
open ExactSixState
open ExactSixStateTyped
open ExactSixStateRecurrentGeometry
open ExactSixStateObservedGR
open ExactSixStateTargetDisruption
open FrozenObservedEvent
open FiniteCanonicalPath
open FiniteEventuallyObserved
open RecurrentClassDecomposition

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

abbrev SixY := JointState Unit (Fin 6)

/-- Frozen for BOTH models, including the original Boolean observation. -/
def eventuallyTrue : Set (ℕ → SixY) :=
  eventuallyObserved observedDescriptor true

def eventuallyFalse : Set (ℕ → SixY) :=
  eventuallyObserved observedDescriptor false

theorem eventuallyTrue_measurable : MeasurableSet eventuallyTrue := by
  exact eventuallyObserved_measurable observedDescriptor true
    Measurable.of_discrete

theorem eventuallyFalse_measurable : MeasurableSet eventuallyFalse := by
  exact eventuallyObserved_measurable observedDescriptor false
    Measurable.of_discrete

theorem eventuallyTrueFalse_disjoint :
    Disjoint eventuallyTrue eventuallyFalse :=
  eventuallyObserved_true_false_disjoint observedDescriptor

/-- This full-path functional is predeclared from the ORIGINAL descriptor.
It is exactly the same function when passed a baseline or perturbed law. -/
noncomputable def fixedProperty : RegimePropertyMap SixY ℝ :=
  eventuallyObservedProperty observedDescriptor true

/-- Baseline six-state dynamics eventually have TRUE observation a.s.
from EVERY physical start, not only the selected comparison basin. -/
theorem baseline_eventually_true_ae (y : SixY) :
    ∀ᵐ w ∂typedModel.pathLaw (Measure.dirac y),
      w ∈ eventuallyTrue := by
  have h := canonical_eventually_observed_ae
    typedModel.inducedKernel observedDescriptor
    (fun z hz => recurrent_observed_true z hz)
    (diracProba y)
  change ∀ᵐ w ∂typedModel.pathLaw (Measure.dirac y),
    w ∈ eventuallyTrue at h
  exact h

/-- True infinite-path EVENT probability (not merely a simulated
hitting frequency). -/
theorem baseline_event_probability_one (y : SixY) :
    typedModel.pathLaw (Measure.dirac y) eventuallyTrue = 1 := by
  let P := typedModel.pathLaw (Measure.dirac y)
  have hAE := baseline_eventually_true_ae y
  rw [ae_iff] at hAE
  have hzero : P eventuallyTrueᶜ = 0 := by
    simpa only [P, Set.compl_setOf] using hAE
  have hsum := measure_add_measure_compl eventuallyTrue_measurable (μ := P)
  rw [hzero] at hsum
  simpa using hsum

/-- Intervened canonical trajectories started at u or a0 are
eventually FALSE under the UNCHANGED observation, almost surely. -/
theorem intervened_eventually_false_ae (i : Fin 6)
    (hi : i = 1 ∨ i = 2) :
    ∀ᵐ w ∂disruptedModel.pathLaw (Measure.dirac (decode i)),
      w ∈ eventuallyFalse := by
  have h := eventually_false_ae i hi
  change ∀ᵐ w ∂disruptedModel.pathLaw (Measure.dirac (decode i)),
    w ∈ eventuallyFalse at h
  exact h

theorem intervened_event_probability_zero (i : Fin 6)
    (hi : i = 1 ∨ i = 2) :
    disruptedModel.pathLaw (Measure.dirac (decode i))
      eventuallyTrue = 0 := by
  let P := disruptedModel.pathLaw (Measure.dirac (decode i))
  have hAE := intervened_eventually_false_ae i hi
  have hnot :
      ∀ᵐ w ∂P, w ∉ eventuallyTrue := by
    filter_upwards [hAE] with w hw
    exact fun ht => Set.disjoint_left.mp eventuallyTrueFalse_disjoint ht hw
  rw [ae_iff] at hnot
  change P {w : ℕ → SixY | ¬ (w ∉ eventuallyTrue)} = 0 at hnot
  simpa only [not_not, Set.setOf_mem_eq] using hnot

/-- Both properties are values of the SAME predeclared path-law map. -/
theorem baselineProperty_one (y : SixY) :
    baselinePropertyValue fixedProperty typedModel y = 1 := by
  change (typedModel.pathLaw (Measure.dirac y) eventuallyTrue).toReal = 1
  rw [baseline_event_probability_one y]
  norm_num

theorem intervenedProperty_zero (i : Fin 6)
    (hi : i = 1 ∨ i = 2) :
    intervenedPropertyValue fixedProperty intervention.intervention
      (decode i) = 0 := by
  change ((intervention.intervention.apply.pathLaw
      (Measure.dirac (decode i))) eventuallyTrue).toReal = 0
  rw [intervention_apply]
  rw [intervened_event_probability_zero i hi]
  norm_num

/-- Direct typed admissibility and world/update-kernel preservation. -/
theorem actual_world_fixed :
    intervention.intervention.apply.world = typedModel.world := by
  rw [intervention_apply]
  exact intervention_world_fixed

theorem actual_update_fixed :
    intervention.intervention.apply.generator.update =
      typedModel.generator.update := by
  rw [intervention_apply]
  exact intervention_update_fixed

end
end TypedEventResponse
end MultipleLimit
end PermanssonResearch
