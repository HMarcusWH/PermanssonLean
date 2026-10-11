import PermanssonResearch.MultipleLimit.TypedEventualHitting
import Mathlib.Tactic

/-!
# Lane C1 — concrete uniform two-step absorption certificate

Unlike a generic kernel lemma with an assumed block bound, this proves a
uniform one-half two-step **hitting** probability for every actual physical
initial state, using the genuine infinite alpha/P/U canonical path measure
and the already-certified exact rational first-hitting recurrences.
It is not an independence assumption or an assertion that arbitrary
absorbing families enjoy a uniform block probability.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedTwoStepAbsorption

open TypedStrategicWitness TypedEventualHitting

/-- Every point start of the genuine model has at least one-half chance
of visiting an absorbing state by time two, counting time zero. -/
theorem typed_two_step_hitting_ge_half (y : Y) :
    (model.pathLaw (Measure.dirac y)).real (hitEvent 2) ≥ (1/2 : ℝ) := by
  rcases y with ⟨ys, yx⟩
  cases ys <;> cases yx
  · change (1/2 : ℝ) ≤
      (model.pathLaw (Measure.dirac t)).real (hitEvent 2)
    change (1/2 : ℝ) ≤
      (model.pathLaw (Measure.dirac t)).real (hitEvent (1+1))
    rw [point_hitting_t_real]
    norm_num
  · change (1/2 : ℝ) ≤
      (model.pathLaw (Measure.dirac u)).real (hitEvent 2)
    rw [point_hitting_u_real]
    norm_num
  · change (1/2 : ℝ) ≤
      (model.pathLaw (Measure.dirac a)).real (hitEvent 2)
    rw [point_hitting_a_real]
    norm_num
  · change (1/2 : ℝ) ≤
      (model.pathLaw (Measure.dirac b)).real (hitEvent 2)
    rw [point_hitting_b_real]
    norm_num

end TypedTwoStepAbsorption
end MultipleLimit
end PermanssonResearch
