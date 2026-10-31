import PermanssonResearch.ApplicationBridge.ControlTableReceipt
import PermanssonResearch.ReverseSolver.RectangularGameLaw
import Mathlib.Tactic

/-!
# ApplicationBridge — rectangular robust-nature table receipts

In Research's finite rectangular game nature observes the realized control
and then selects a physical row, independently at every chronological node;
both players may use behavioral strategies on complete histories. A receipt
reports the value table by remaining steps.

`RectTableChecks` decides that the table starts at the terminal reward and
that every entry is the max over admitted controls of the min over admitted
nature rows (`rectStep`, computable `sup'`/`inf'`). `checked_table_eq_value`
identifies the checked table with Research's `value`, and
`checked_rectangular_saddle` transfers `rectangular_game_actual_saddle`: some
controller guarantees the checked value against every nature strategy, and
some nature strategy holds every controller to it, on the actual
chronological product law. The same check with a single admitted control per
state evaluates a fixed policy against rectangular nature, and with a single
nature row additionally evaluates it under one committed model. Private-stage
and committed-game optimality are not claimed.
-/

namespace PermanssonResearch.ApplicationBridge.RobustReceipt

open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.RectangularFiniteGame

set_option autoImplicit false

variable {C Θ : Type*} [DecidableEq C] [DecidableEq Θ] [Fintype C] [Fintype Θ] {n : ℕ}

/-- Computable rectangular Bellman step at time `t`. -/
def rectStep (G : Game C Θ n) (v : Fin n → ℚ) (t : ℕ) (y : Fin n) : ℚ :=
  (G.options y).sup' (G.options_nonempty y) (fun c =>
    (G.natureOptions t y c).inf' (G.nature_nonempty t y c) (fun θ => rowScore G v t y c θ))

theorem minScore_eq_inf' (G : Game C Θ n) (v : Fin n → ℚ) (t : ℕ) (y : Fin n) (c : C) :
    minScore G v t y c =
      (G.natureOptions t y c).inf' (G.nature_nonempty t y c) (fun θ => rowScore G v t y c θ) := by
  apply le_antisymm
  · exact Finset.le_inf' _ _ (fun θ hθ => minScore_le_row G v t y c θ hθ)
  · exact Finset.inf'_le _ (minimizingRow_mem G v t y c)

theorem maxmin_eq_rectStep (G : Game C Θ n) (v : Fin n → ℚ) (t : ℕ) (y : Fin n) :
    minScore G v t y (maximizingControl G v t y) = rectStep G v t y := by
  unfold rectStep
  apply le_antisymm
  · rw [minScore_eq_inf']
    exact Finset.le_sup' (fun c => (G.natureOptions t y c).inf' (G.nature_nonempty t y c)
      (fun θ => rowScore G v t y c θ)) (maximizingControl_mem G v t y)
  · apply Finset.sup'_le
    intro c hc
    rw [← minScore_eq_inf']
    exact minScore_le_max G v t y c hc

/-- The table starts at the terminal reward and follows the rectangular
    max-min recursion; entry `r` is used at time `N - r`. -/
def RectTableChecks (G : Game C Θ n) (reward : Fin n → ℚ) (N : ℕ)
    (table : ℕ → Fin n → ℚ) : Prop :=
  (∀ y, table 0 y = reward y) ∧
  ∀ r : Fin N, ∀ y, table (r.val + 1) y = rectStep G (table r.val) (N - (r.val + 1)) y

instance (G : Game C Θ n) (reward : Fin n → ℚ) (N : ℕ) (table : ℕ → Fin n → ℚ) :
    Decidable (RectTableChecks G reward N table) := by
  unfold RectTableChecks
  infer_instance

def checkRectangularTable (G : Game C Θ n) (reward : Fin n → ℚ) (N : ℕ)
    (table : ℕ → Fin n → ℚ) : Bool :=
  decide (RectTableChecks G reward N table)

omit [Fintype C] [Fintype Θ] in
theorem checkRectangularTable_sound (G : Game C Θ n) (reward : Fin n → ℚ) (N : ℕ)
    (table : ℕ → Fin n → ℚ) (h : checkRectangularTable G reward N table = true) :
    RectTableChecks G reward N table := by
  unfold checkRectangularTable at h
  exact of_decide_eq_true h

/-- A checked table is Research's rectangular value at the matching time. -/
theorem checked_table_eq_value (G : Game C Θ n) (reward : Fin n → ℚ) (N : ℕ)
    (table : ℕ → Fin n → ℚ) (h : checkRectangularTable G reward N table = true) :
    ∀ r, r ≤ N → ∀ y, value G reward r (N - r) y = table r y := by
  obtain ⟨h0, hstep⟩ := checkRectangularTable_sound G reward N table h
  intro r
  induction r with
  | zero => intro _ y; rw [h0 y]; rfl
  | succ r ih =>
    intro hr y
    have hprev : value G reward r (N - (r + 1) + 1) = table r := by
      have ht : N - (r + 1) + 1 = N - r := by omega
      funext z
      rw [ht]
      exact ih (by omega) z
    change minScore G (value G reward r (N - (r + 1) + 1)) (N - (r + 1)) y
        (maximizingControl G (value G reward r (N - (r + 1) + 1)) (N - (r + 1)) y) = _
    rw [hprev, maxmin_eq_rectStep, hstep ⟨r, by omega⟩ y]

/-- The checked value is the saddle value of the actual chronological game:
    some controller guarantees it against every nature strategy, and some
    nature strategy holds every controller to it. -/
theorem checked_rectangular_saddle (G : Game C Θ n) (reward : Fin n → ℚ) (N : ℕ)
    (table : ℕ → Fin n → ℚ) (h : checkRectangularTable G reward N table = true) (y : Fin n) :
    (∃ σ : Controller G, ∀ η : Nature G,
      (table N y : ℝ) ≤ gameExpectation G reward σ η N 0 (y, []) y) ∧
    (∃ η : Nature G, ∀ σ : Controller G,
      gameExpectation G reward σ η N 0 (y, []) y ≤ (table N y : ℝ)) := by
  have hv : value G reward N 0 y = table N y := by
    have := checked_table_eq_value G reward N table h N le_rfl y
    simpa using this
  obtain ⟨hup, hlow, -⟩ := rectangular_game_actual_saddle G reward N y
  rw [hv] at hup hlow
  exact ⟨⟨_, hlow⟩, ⟨_, hup⟩⟩

end PermanssonResearch.ApplicationBridge.RobustReceipt
