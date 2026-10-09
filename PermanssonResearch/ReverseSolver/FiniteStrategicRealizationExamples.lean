import PermanssonResearch.ReverseSolver.FiniteStrategicRealization
import PermanssonResearch.ReverseSolver.CertificationExamples
import Mathlib.Tactic

/-!
# D0-D finite typed construction: two distinguishable rational strategies

Unlike the standalone D0-B matrices, these are actual canonical strategic-world
models and a genuine admissible action-selection intervention with fixed P and U.
At starting world state 0, the baseline half-goal row assigns mass 1/2 to goal
world state 1; the strategic replacement assigns mass 1.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace ReverseSolver
namespace FiniteStrategicRealizationExamples

open FiniteStrategicRealization

noncomputable section

def halfModel :=
  realizedModel RationalExamples.halfGoalMatrix

def sureReplacement :=
  rationalStrategicIntervention
    RationalExamples.halfGoalMatrix RationalExamples.sureGoalMatrix

/-- The BASELINE typed alpha/P/U process has one-half probability of
entering world state 1 from 0 in one transition. -/
theorem half_model_encoded_goal :
    halfModel.inducedKernel (decode (0 : Fin 2))
        (encode ⁻¹' ({1} : Set (Fin 2))) = 1 / 2 := by
  change (realizedModel RationalExamples.halfGoalMatrix).inducedKernel
    (decode (0 : Fin 2)) (encode ⁻¹' ({1} : Set (Fin 2))) = 1 / 2
  rw [inducedKernel_encodedEntry]
  norm_num [RationalExamples.halfGoalMatrix]

/-- The ADMISSIBLE strategic replacement has goal probability exactly one.
The world primitive is identical to the baseline by type. -/
theorem sure_intervened_encoded_goal :
    sureReplacement.intervention.apply.inducedKernel (decode (0 : Fin 2))
        (encode ⁻¹' ({1} : Set (Fin 2))) = 1 := by
  change (rationalStrategicIntervention
      RationalExamples.halfGoalMatrix RationalExamples.sureGoalMatrix)
    .intervention.apply.inducedKernel
      (decode (0 : Fin 2)) (encode ⁻¹' ({1} : Set (Fin 2))) = 1
  rw [intervenedKernel_worldCylinder
    RationalExamples.halfGoalMatrix RationalExamples.sureGoalMatrix
    (0 : Fin 2) (measurableSet_singleton (1 : Fin 2))]
  rw [rationalFiniteKernel_singleton]
  norm_num [RationalExamples.sureGoalMatrix]

/-- This is a genuinely nonzero effect on an encoded event,
not a vacuous relabeling of two identical kernels. -/
theorem two_typed_models_have_distinct_goal_probability :
    halfModel.inducedKernel (decode (0 : Fin 2))
      (encode ⁻¹' ({1} : Set (Fin 2))) ≠
    sureReplacement.intervention.apply.inducedKernel (decode (0 : Fin 2))
      (encode ⁻¹' ({1} : Set (Fin 2))) := by
  rw [half_model_encoded_goal, sure_intervened_encoded_goal]
  norm_num

/-- The whole construction enforces the hold-P-fixed semantics. -/
theorem replacement_preserves_world :
    sureReplacement.intervention.apply.world = halfModel.world :=
  rationalStrategicIntervention_world_fixed _ _

/-- The strategic update kernel is also fixed. -/
theorem replacement_preserves_update :
    sureReplacement.intervention.apply.generator.update =
      halfModel.generator.update :=
  rationalStrategicIntervention_update_fixed _ _

end
end FiniteStrategicRealizationExamples
end ReverseSolver
end PermanssonResearch
