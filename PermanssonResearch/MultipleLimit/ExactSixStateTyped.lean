import PermanssonResearch.MultipleLimit.ExactSixStateCanonical
import PermanssonResearch.ReverseSolver.FiniteStrategicPathBridge
import Mathlib.Tactic

/-!
# Lane C2 — genuine typed alpha/P/U six-state canonical hitting

The original D0-D construction realizes ANY certified rational Markov matrix
as a typed strategic-world process: alpha samples actions, P copies actions
to world, U updates Unit memory. The original D0-E theorem proves
ALL-horizon finite-prefix canonical path transport.

Instantiating these existing theorems on our six-state matrix is an actual
typed bridge, not an independent unverified reference matrix. It does not
establish the infinite-path random occupation law.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateTyped

open ReverseSolver
open ReverseSolver.FiniteStrategicRealization
open ReverseSolver.FiniteStrategicPathBridge
open ExactSixStateCanonical
open PermanssonLean

noncomputable def typedModel :=
  realizedModel sixStateMatrix

theorem typedKernel_worldCylinder
    (i : Fin 6) {E : Set (Fin 6)} (hE : MeasurableSet E) :
    typedModel.inducedKernel (decode i) (encode ⁻¹' E) =
      rationalFiniteKernel sixStateMatrix i E := by
  exact inducedKernel_worldCylinder sixStateMatrix i hE

/-- Actual typed alpha/P/U hitting probability equals the independent
six-state rational recurrence for EVERY finite horizon. -/
theorem typed_hitting_all_horizons (i : Fin 6) (T : ℕ) :
    hittingValue (typedTarget recurrentTarget) typedModel.inducedKernel
      (decode i) T =
    (rationalHittingValue sixStateMatrix recurrentTarget T i : ℝ) := by
  exact typedHittingValue_eq_rational_all_horizons
    sixStateMatrix recurrentTarget i T

theorem typed_t_two_step_hit :
    hittingValue (typedTarget recurrentTarget) typedModel.inducedKernel
      (decode (0 : Fin 6)) 2 = (1/2 : ℝ) := by
  rw [typed_hitting_all_horizons]
  norm_num [t_two_step_hit]

theorem typed_u_two_step_hit :
    hittingValue (typedTarget recurrentTarget) typedModel.inducedKernel
      (decode (1 : Fin 6)) 2 = (3/4 : ℝ) := by
  rw [typed_hitting_all_horizons]
  norm_num [u_two_step_hit]


/-- Uniform two-transition finite-horizon bound on the ACTUAL typed
strategic-world process, obtained without a sampling approximation. -/
theorem typed_two_step_hit_at_least_half (i : Fin 6) :
    (1/2 : ℝ) ≤
      hittingValue (typedTarget recurrentTarget) typedModel.inducedKernel
        (decode i) 2 := by
  rw [typed_hitting_all_horizons]
  exact_mod_cast two_step_hit_at_least_half i

end ExactSixStateTyped
end MultipleLimit
end PermanssonResearch
