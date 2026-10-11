import PermanssonResearch.MultipleLimit.TypedObservedExactGR
import PermanssonLean.Regime.ExitTime
import Mathlib.Tactic

/-!
# Lane C1 — explicit confirmatory descriptor nondegeneracy

For the nonconstant frozen observation descriptor, two basin-reachable
point-started time-zero descriptor laws differ.  This strengthens the
formal Exact GR certificate to the existing confirmatory GR subclass.
It does not claim a constitutive strategic intervention or empirical PR.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedObservedConfirmatory

open TypedStrategicWitness TypedObservedExactGR
open PermanssonLean PermanssonLean.RegimeSpecification

noncomputable section

/-- The actual canonical descriptor distribution at time zero is the
Dirac measure of the frozen descriptor at its deterministic initial point. -/
theorem observed_descriptorLaw_zero (y : Y) :
    descriptorLaw model observedSpec (diracProba y) 0 =
      diracProba (observedSpec.descriptor y) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun w : ℕ → Y => observedSpec.descriptor (w 0))
      (model.pathLaw (Measure.dirac y)) =
    Measure.dirac (observedSpec.descriptor y)
  calc
    Measure.map (fun w : ℕ → Y => observedSpec.descriptor (w 0))
        (model.pathLaw (Measure.dirac y)) =
      Measure.map observedSpec.descriptor
        ((model.pathLaw (Measure.dirac y)).map (fun w : ℕ → Y => w 0)) := by
          rw [Measure.map_map observedSpec.descriptor_measurable
            (measurable_pi_apply 0)]
          rfl
    _ = Measure.map observedSpec.descriptor (Measure.dirac y) := by
      rw [StrategicWorldModel.pathLaw_eval_zero]
    _ = Measure.dirac (observedSpec.descriptor y) := by
      simp

/-- Distinct descriptor laws are reachable from the declared basin,
already at the predeclared time-zero coordinate. -/
theorem observed_descriptorNondegenerate :
    IsDescriptorNondegenerate model observedSpec := by
  refine ⟨t, by simp [observedSpec], 0,
    a, by simp [observedSpec], 0, ?_⟩
  rw [observed_descriptorLaw_zero, observed_descriptorLaw_zero]
  change diracProba (false : Bool) ≠ diracProba true
  intro h
  have hab : (false : Bool) = true := injective_diracProba h
  cases hab

/-- An explicitly stronger existing formal classifier; not a
Permansson constitutive-intervention or empirical certificate. -/
theorem observedConfirmatoryGeneratedRegime :
    IsConfirmatoryGeneratedRegime model observedSpec observedReference :=
  ⟨observedExactGeneratedRegime, observed_descriptorNondegenerate⟩

end
end TypedObservedConfirmatory
end MultipleLimit
end PermanssonResearch
