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


/-- A *nonconstant* fixed descriptor on the complete four-state strategic
space. It distinguishes transient from absorbing regime membership while
identifying both distinct physical absorbing outcomes. -/
def nonconstantAbsorptionDescriptor (y : Y) : Bool := y.1

/-- The descriptor has at least two values on the full finite state space.
This is the nontriviality that the earlier constant collapse lacked. -/
theorem nonconstantAbsorptionDescriptor_two_values :
    ∃ y z : Y,
      nonconstantAbsorptionDescriptor y ≠ nonconstantAbsorptionDescriptor z := by
  exact ⟨(false, false), (true, false), by decide⟩

theorem nonconstantAbsorptionDescriptor_collapses :
    absorbingA ≠ absorbingB ∧
      nonconstantAbsorptionDescriptor absorbingA =
        nonconstantAbsorptionDescriptor absorbingB := by
  exact ⟨absorbingA_ne_absorbingB, rfl⟩

/-- Physical terminal measures remain different, but the frozen nonconstant
descriptor pushes both to the same observed terminal probability measure. -/
theorem nonconstantAbsorptionDescriptor_terminal_laws :
    (terminalLaw absorbingA).map nonconstantAbsorptionDescriptor =
      (terminalLaw absorbingB).map nonconstantAbsorptionDescriptor := by
  rw [terminalLaw_descriptor_apply, terminalLaw_descriptor_apply]
  rfl

end MultipleLimit
end PermanssonResearch
