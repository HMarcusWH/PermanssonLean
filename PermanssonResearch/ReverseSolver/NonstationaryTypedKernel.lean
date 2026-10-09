import PermanssonResearch.ReverseSolver.NonstationaryOptimality
import PermanssonResearch.ReverseSolver.ControlledKernelCorrespondence
import Mathlib.Tactic

/-!
# D1-C2: time-indexed genuine strategic-world induced kernels

Each elapsed-time kernel is the ACTUAL canonical alpha -> P -> U
induced kernel of the constructed Unit × Fin n feedbackModel. The original
deadline D stays fixed; elapsed step i selects the remaining-horizon
policy pi (D-i). The only changed primitive is alpha. The constructed
world-transition P and strategic update U are invariant across every
selected step and agree with the baseline's P and U.

No time-varying sequence is misrepresented as one frozen intervention.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace NonstationaryTyped

open Bellman
open ControlledKernel
open FiniteStrategicRealization
open FiniteStrategicPathBridge
open Nonstationary
open PermanssonLean

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

universe uC

/-- The actual typed strategic-world model selected at elapsed time i. -/
noncomputable def selectedModel {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D i : ℕ) :=
  feedbackModel sys (pi (D-i))

/-- Canonically composed alpha/P/U induced kernel, not a rational surrogate. -/
noncomputable def selectedTypedKernel {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D i : ℕ) :
    Kernel (JointState Unit (Fin n)) (JointState Unit (Fin n)) :=
  (selectedModel sys pi D i).inducedKernel

instance selectedTypedKernel_isMarkov {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D i : ℕ) : IsMarkovKernel (selectedTypedKernel sys pi D i) := by
  unfold selectedTypedKernel
  infer_instance

/-- The P component is the same typed primitive at each time and equals
the original baseline's P. -/
theorem selected_world_fixed {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D i : ℕ) :
    (selectedModel sys pi D i).world =
      (realizedModel sys.baseline).world := by
  exact feedback_preserves_world sys (pi (D-i))

/-- The strategic update U likewise never changes with the deadline,
elapsed time, or chosen admissible feedback rule. -/
theorem selected_update_fixed {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D i : ℕ) :
    (selectedModel sys pi D i).generator.update =
      (realizedModel sys.baseline).generator.update := by
  exact feedback_preserves_update sys (pi (D-i))

/-- The actual typed one-step event mass equals the D1-C1 selected
rational transition row, at the SAME deadline and elapsed time. -/
theorem selectedTypedKernel_encodedEntry
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D i : ℕ) (y z : Fin n) :
    selectedTypedKernel sys pi D i (decode y)
        (encode ⁻¹' ({z} : Set (Fin n))) =
      ENNReal.ofReal ((selectedMatrix sys pi D i).entry y z : ℝ) := by
  change (feedbackModel sys (pi (D-i))).inducedKernel (decode y)
      (encode ⁻¹' ({z} : Set (Fin n))) =
    ENNReal.ofReal ((feedbackMatrix sys (pi (D-i))).entry y z : ℝ)
  exact feedback_induced_encodedEntry sys (pi (D-i)) y z

/-- The stronger full measurable next-world event correspondence,
which is sufficient for all finite atom and path-law transport. -/
theorem selectedTypedKernel_worldCylinder
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D i : ℕ) (y : Fin n) {E : Set (Fin n)} (hE : MeasurableSet E) :
    selectedTypedKernel sys pi D i (decode y) (encode ⁻¹' E) =
      selectedKernel sys pi D i y E := by
  change (feedbackModel sys (pi (D-i))).inducedKernel (decode y)
      (encode ⁻¹' E) =
    rationalFiniteKernel (feedbackMatrix sys (pi (D-i))) y E
  change (realizedModel (feedbackMatrix sys (pi (D-i)))).inducedKernel
    (decode y) (encode ⁻¹' E) =
    rationalFiniteKernel (feedbackMatrix sys (pi (D-i))) y E
  exact inducedKernel_worldCylinder _ y hE

/-- Singleton typed next-state mass is equal to the genuine selected
rational atom. This uses the actual Unit × Fin n joint-state encoding. -/
theorem selectedTypedKernel_decode_singleton
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D i : ℕ) (y z : Fin n) :
    selectedTypedKernel sys pi D i (decode y) {decode z} =
      selectedKernel sys pi D i y {z} := by
  have hset : encode ⁻¹' ({z} : Set (Fin n)) = {decode z} := by
    ext p
    rcases p with ⟨u,v⟩
    cases u
    simp [encode,decode]
  rw [← hset]
  exact selectedTypedKernel_worldCylinder sys pi D i y (measurableSet_singleton z)

end NonstationaryTyped
end ReverseSolver
end PermanssonResearch
