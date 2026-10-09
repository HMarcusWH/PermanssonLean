import PermanssonResearch.ReverseSolver.FiniteStrategicRealization
import Mathlib.Tactic

/-!
# D1-A: finite fully observed state-feedback control

This begins a NEW research-only controlled-process layer. A control is
selected from the state-dependent nonempty admissible set BEFORE the action.
Every control chooses a certified finite rational action-selection kernel;
the canonical strategic-world primitive P and update U remain fixed.

This first construction is for the concrete Unit × Fin n typed realization.
It is NOT a D0 FrozenMenu member held fixed across the trajectory, nor a
claim about arbitrary external alpha/P/U models. Bellman optimality and
time-dependent policies are later D1 milestones.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace ControlledKernel

open FiniteStrategicRealization

universe uC

/-- A nonempty permitted control set at EACH finite joint state. Controls
index stationary replacement action-selection kernels, but the controller
may choose a different kernel at each encountered state. -/
structure FiniteControlSystem (C : Type uC) [DecidableEq C] (n : ℕ) where
  baseline : RationalMarkovMatrix n
  options : Fin n → Finset C
  options_nonempty : ∀ y : Fin n, (options y).Nonempty
  matrix : C → RationalMarkovMatrix n

/-- A fully observed state-feedback selection with a proof that every local
choice is admissible. The control type need not enumerate all possible
interventions; only explicitly permitted indices may be selected. -/
structure StateFeedback {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) where
  choose : Fin n → C
  permitted : ∀ y : Fin n, choose y ∈ sys.options y

/-- The precise D1 row law: choose a control from the CURRENT state,
then draw the successor under that control's row. This is time-homogeneous
only because this first feedback policy is a fixed function of state. -/
def feedbackMatrix {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : StateFeedback sys) :
    RationalMarkovMatrix n where
  entry := fun y z => (sys.matrix (π.choose y)).entry y z
  entry_nonneg := by
    intro y z
    exact (sys.matrix (π.choose y)).entry_nonneg y z
  row_sum_one := by
    intro y
    exact (sys.matrix (π.choose y)).row_sum_one y

@[simp] theorem feedbackMatrix_entry {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : StateFeedback sys)
    (y z : Fin n) :
    (feedbackMatrix sys π).entry y z =
      (sys.matrix (π.choose y)).entry y z := rfl

/-- Every selected row is nonnegative. -/
theorem feedback_entry_nonneg {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : StateFeedback sys)
    (y z : Fin n) :
    0 ≤ (feedbackMatrix sys π).entry y z :=
  (feedbackMatrix sys π).entry_nonneg y z

/-- Every selected row is normalized, regardless of which control was
admissibly selected at other states. -/
theorem feedback_row_sum_one {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : StateFeedback sys)
    (y : Fin n) :
    (∑ z : Fin n, (feedbackMatrix sys π).entry y z) = 1 :=
  (feedbackMatrix sys π).row_sum_one y

/-- A fixed control induces exactly its original kernel if the control is
allowed at all states. This separates fixed D0-style choices from feedback. -/
def constantFeedback {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (c : C)
    (hc : ∀ y : Fin n, c ∈ sys.options y) : StateFeedback sys where
  choose := fun _ => c
  permitted := hc

theorem feedbackMatrix_constant {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (c : C)
    (hc : ∀ y : Fin n, c ∈ sys.options y) :
    (feedbackMatrix sys (constantFeedback sys c hc)).entry =
      (sys.matrix c).entry := rfl

/-- The canonical typed realization of the genuine state-feedback kernel.
The world primitive copies selected actions, and the update U is unchanged. -/
noncomputable def feedbackModel {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : StateFeedback sys) :=
  realizedModel (feedbackMatrix sys π)

/-- P remains the BASELINE world primitive. This holds by construction,
not by interpreting feedback as a single original frozen intervention. -/
theorem feedback_preserves_world {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : StateFeedback sys) :
    (feedbackModel sys π).world = (realizedModel sys.baseline).world :=
  realizedModel_world_fixed _ _

/-- The strategic memory update U remains the BASELINE update primitive. -/
theorem feedback_preserves_update {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : StateFeedback sys) :
    (feedbackModel sys π).generator.update =
      (realizedModel sys.baseline).generator.update := rfl

end ControlledKernel
end ReverseSolver
end PermanssonResearch
