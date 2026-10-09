import PermanssonResearch.ReverseSolver.ControlledKernel
import PermanssonResearch.ReverseSolver.FiniteStrategicPathBridge
import Mathlib.Tactic

/-!
# D1-A: canonical one-step and all-horizon correspondence

For a fixed fully observed state-feedback selector, row-by-row control
choices form one Markov kernel. At EACH starting state the selected one-step
row equals the actual canonical alpha -> P -> U intervention obtained by
freezing the control selected at that state.

The entire feedback law is NOT asserted to be any single frozen D0 member.
The constructed feedback kernel has its own valid canonical prefix law.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace ControlledKernel

open FiniteStrategicRealization
open FiniteStrategicPathBridge

universe uC

noncomputable section

/-- Exact canonical one-step atom from the feedback strategic-world model:
the chosen action-selection control precedes the unchanged world kernel P
and unchanged strategic update U. -/
theorem feedback_induced_encodedEntry {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : StateFeedback sys)
    (x z : Fin n) :
    (feedbackModel sys π).inducedKernel
        (decode x) (encode ⁻¹' ({z} : Set (Fin n))) =
      ENNReal.ofReal ((sys.matrix (π.choose x)).entry x z : ℝ) := by
  change (realizedModel (feedbackMatrix sys π)).inducedKernel
    (decode x) (encode ⁻¹' ({z} : Set (Fin n))) = _
  rw [inducedKernel_encodedEntry]
  rfl

/-- Stronger than atomwise equality: on every measurable encoded next-world
event, the controlled canonical induced kernel at current state x equals the
D0 canonical induced kernel of the control frozen at that SAME current state.
The equality is statewise, not a claim that a single frozen intervention
reproduces an adaptive feedback trajectory. -/
theorem feedback_agrees_with_frozen_at_state
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : StateFeedback sys)
    (x : Fin n) {D : Set (Fin n)} (hD : MeasurableSet D) :
    (feedbackModel sys π).inducedKernel (decode x) (encode ⁻¹' D) =
      (rationalStrategicIntervention sys.baseline
        (sys.matrix (π.choose x))).intervention.apply.inducedKernel
        (decode x) (encode ⁻¹' D) := by
  change (realizedModel (feedbackMatrix sys π)).inducedKernel
    (decode x) (encode ⁻¹' D) = _
  rw [rationalStrategicIntervention_applied]
  rw [inducedKernel_worldCylinder (feedbackMatrix sys π) x hD]
  rw [inducedKernel_worldCylinder (sys.matrix (π.choose x)) x hD]
  rfl

/-- The feedback model's actual encoded finite-prefix law is the canonical
finite-prefix law of the statewise selected rational Markov matrix, at every
finite horizon. This does not certify arbitrary nonstationary controllers. -/
theorem feedback_prefixLaw_transport
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : StateFeedback sys)
    (x : Fin n) (T : ℕ) :
    (PermanssonLean.ProbabilitySupport.finitePrefixLaw
      (feedbackModel sys π).inducedKernel (decode x) T).map
        (prefixEncode T) =
      PermanssonLean.ProbabilitySupport.finitePrefixLaw
        (rationalFiniteKernel (feedbackMatrix sys π)) x T :=
  realized_prefixLaw_map (feedbackMatrix sys π) x T

/-- All-horizon canonical typed target-before-forbidden value equals the
exact finite rational recursion for THIS constructed state-feedback kernel.
It proves value correspondence, not optimality among feedback policies. -/
theorem feedback_typed_hitting_value
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : StateFeedback sys)
    (rt : RationalHittingTarget n) (x : Fin n) (T : ℕ) :
    hittingValue (typedTarget rt) (feedbackModel sys π).inducedKernel
        (decode x) T =
      (rationalHittingValue (feedbackMatrix sys π) rt T x : ℝ) :=
  typedHittingValue_eq_rational_all_horizons (feedbackMatrix sys π) rt x T

end
end ControlledKernel
end ReverseSolver
end PermanssonResearch
