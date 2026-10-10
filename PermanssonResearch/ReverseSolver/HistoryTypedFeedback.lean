import PermanssonResearch.ReverseSolver.HistoryPrefixKernel
import PermanssonResearch.ReverseSolver.ControlledKernelCorrespondence
import Mathlib.Tactic

/-!
# D1-D2: admissible historical action to globally valid feedback

The observed state's control is exactly the complete-history choice;
all unvisited rows use admissible fillers selected independently.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependentTyped

open HistoryDependent ControlledKernel FiniteStrategicRealization
universe uC

/-- An admissible feedback extension of the action chosen at a supplied
history, with no global admissible-control or finite-C assumption. -/
noncomputable def historyFeedback {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (h : History n i) : StateFeedback sys where
  choose := fun z =>
    if hz : z = HistoryDependent.last h then
      σ.choose D i h
    else Classical.choose (sys.options_nonempty z)
  permitted := by
    intro z
    split_ifs with hz
    · simpa [hz] using σ.permitted D i h
    · exact Classical.choose_spec (sys.options_nonempty z)

/-- The selected control does not depend on the auxiliary rows. -/
@[simp] theorem historyFeedback_choose_current
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (h : History n i) :
    (historyFeedback sys σ D i h).choose (HistoryDependent.last h) =
      σ.choose D i h := by
  simp [historyFeedback]

/-- The actual selected rational row is exactly the history policy's row. -/
theorem historyFeedback_current_row
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (h : History n i) (z : Fin n) :
    (feedbackMatrix sys (historyFeedback sys σ D i h)).entry
        (HistoryDependent.last h) z =
      HistoryDependent.selectedEntry sys σ D i h z := by
  rw [feedbackMatrix_entry, historyFeedback_choose_current]
  rfl

/-- The WHOLE successor probability measure is independent of the choices
made at the states outside the observed current state. -/
theorem historyFeedback_current_measure
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D i : ℕ) (h : History n i) :
    rationalFiniteKernel
      (feedbackMatrix sys (historyFeedback sys σ D i h))
      (HistoryDependent.last h) =
    rationalFiniteKernel (sys.matrix (σ.choose D i h))
      (HistoryDependent.last h) := by
  classical
  change
    (∑ z : Fin n,
      ENNReal.ofReal
        ((feedbackMatrix sys (historyFeedback sys σ D i h)).entry
          (HistoryDependent.last h) z : ℝ) • Measure.dirac z) =
    (∑ z : Fin n,
      ENNReal.ofReal
        ((sys.matrix (σ.choose D i h)).entry
          (HistoryDependent.last h) z : ℝ) • Measure.dirac z)
  apply Finset.sum_congr rfl
  intro z _
  rw [historyFeedback_current_row]
  rfl

end HistoryDependentTyped
end ReverseSolver
end PermanssonResearch
