import PermanssonResearch.MultipleLimit.Counterexamples
import Mathlib.Tactic

/-!
# Lane C1 — terminal descriptor transport

The endpoint descriptor law is the pushforward of the actual terminal
Dirac measure. Equality of terminal descriptors can collapse distinct
physical absorbing classes, without rewriting the frozen regime descriptor.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit

open PermanssonLean.PeriodicExactGR

theorem terminalLaw_descriptor_apply
    (h : Y → Bool) (a : Y) :
    (terminalLaw a).map h = diracProba (h a) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.dirac a).map h = Measure.dirac (h a)
  exact Measure.map_dirac a

theorem collapsed_observed_terminal_laws :
    (terminalLaw absorbingA).map collapsedDescriptor =
      (terminalLaw absorbingB).map collapsedDescriptor := by
  rw [terminalLaw_descriptor_apply, terminalLaw_descriptor_apply]
  rfl

end MultipleLimit
end PermanssonResearch
