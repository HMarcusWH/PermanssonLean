import PermanssonResearch.ApplicationBridge.GrammarReceipt
import PermanssonResearch.ReverseSolver.MonitorOptimality
import Mathlib.Tactic

/-!
# ApplicationBridge — adaptive admitted-block control receipts

The admitted patch blocks of a grammar receipt become the controls of a
`FiniteControlSystem`: at every step the controller selects a whole admitted
block, whose α/P/U-induced rows then generate the next joint state, and its
full history may select a different block next time. This is the timing of
Research's `AdaptiveGrammarControl`; here each block's rows are the
`inducedMatrix` of a reflected `FiniteWorldInput`, and the per-instance
emitted source proves that the block keeps feasibility and P and is the
baseline with exactly its declared patch rows.

`regionMonitor` carries one flag, "every observed state so far lies in the
region", and rewards survival or exit at the horizon. `MonitorTableChecks`
decides that a reported rational table starts at the reward and follows the
max-over-blocks Bellman step layer by layer; `checked_table_eq_value`
identifies it with Research's `FiniteMonitor.value`, and
`checked_adaptive_optimal` transfers `monitor_optimal_and_attained`: every
real full-history behavioral block controller is bounded by the table value
on the actual chronological trace law, and one attains it. Frozen-block
comparisons, overlap-model atom certificates and empirical identification are
not claimed here.
-/

namespace PermanssonResearch.ApplicationBridge.AdaptiveBlockReceipt

open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.ControlledKernel
open PermanssonResearch.ReverseSolver.FiniteMonitor

set_option autoImplicit false

variable {n k : ℕ}

/-- Every admitted block is available at every joint state. -/
def blockSystem (base : RationalMarkovMatrix n) (members : Fin k → RationalMarkovMatrix n)
    (hk : 0 < k) (hn : 0 < n) : FiniteControlSystem (Fin k) n where
  states_nonempty := hn
  baseline := base
  options := fun _ => Finset.univ
  options_nonempty := fun _ => ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  matrix := members

/-- The flag records that every observed state so far lies in `region`; the
    reward is survival (`survival = true`) or exit by the horizon. -/
def regionMonitor (region : Finset (Fin n)) (survival : Bool) : Monitor (Fin k) n Bool where
  initial y := decide (y ∈ region)
  update _ s _ _ z := s && decide (z ∈ region)
  reward _ s := if s = survival then 1 else 0

section Table

variable {C : Type*} [DecidableEq C] [Fintype C] {S : Type*} [Fintype S]

/-- The reported table starts at the reward and every layer is the
    max-over-admitted-controls step of the previous one; entry `r` is used at
    chronological time `N - r`. -/
def MonitorTableChecks (sys : FiniteControlSystem C n) (M : Monitor C n S) (N : ℕ)
    (table : ℕ → Fin n → S → ℚ) : Prop :=
  (∀ y s, table 0 y s = M.reward y s) ∧
  ∀ r : Fin N, ∀ y s, table (r.val + 1) y s =
    (sys.options y).sup' (sys.options_nonempty y) (score sys M (table r.val) (N - (r.val + 1)) y s)

instance (sys : FiniteControlSystem C n) (M : Monitor C n S) (N : ℕ)
    (table : ℕ → Fin n → S → ℚ) : Decidable (MonitorTableChecks sys M N table) := by
  unfold MonitorTableChecks
  infer_instance

def checkMonitorTable (sys : FiniteControlSystem C n) (M : Monitor C n S) (N : ℕ)
    (table : ℕ → Fin n → S → ℚ) : Bool :=
  decide (MonitorTableChecks sys M N table)

omit [Fintype C] in
theorem checkMonitorTable_sound (sys : FiniteControlSystem C n) (M : Monitor C n S) (N : ℕ)
    (table : ℕ → Fin n → S → ℚ) (h : checkMonitorTable sys M N table = true) :
    MonitorTableChecks sys M N table := by
  unfold checkMonitorTable at h
  exact of_decide_eq_true h

omit [Fintype C] [Fintype S] in
theorem maximizing_eq_sup' (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (v : Fin n → S → ℚ) (t : ℕ) (y : Fin n) (s : S) :
    score sys M v t y s (maximizingControl sys M v t y s) =
      (sys.options y).sup' (sys.options_nonempty y) (score sys M v t y s) :=
  le_antisymm (Finset.le_sup' (score sys M v t y s) (maximizingControl_permitted sys M v t y s))
    (Finset.sup'_le _ _ fun c hc => maximizingControl_dominates sys M v t y s c hc)

omit [Fintype C] in
/-- A checked table is Research's monitor value at the matching time. -/
theorem checked_table_eq_value (sys : FiniteControlSystem C n) (M : Monitor C n S) (N : ℕ)
    (table : ℕ → Fin n → S → ℚ) (h : checkMonitorTable sys M N table = true) :
    ∀ r, r ≤ N → ∀ y s, value sys M r (N - r) y s = table r y s := by
  obtain ⟨h0, hstep⟩ := checkMonitorTable_sound sys M N table h
  intro r
  induction r with
  | zero => intro _ y s; rw [h0 y s]; rfl
  | succ r ih =>
    intro hr y s
    have hprev : value sys M r (N - (r + 1) + 1) = table r := by
      have ht : N - (r + 1) + 1 = N - r := by omega
      funext z q
      rw [ht]
      exact ih (by omega) z q
    change score sys M (value sys M r (N - (r + 1) + 1)) (N - (r + 1)) y s
        (maximizingControl sys M (value sys M r (N - (r + 1) + 1)) (N - (r + 1)) y s) = _
    rw [hprev, maximizing_eq_sup', hstep ⟨r, by omega⟩ y s]

/-- The checked value is the optimum over every real full-history behavioral
    controller on the actual chronological trace law, and it is attained. -/
theorem checked_adaptive_optimal (sys : FiniteControlSystem C n) (M : Monitor C n S) (N : ℕ)
    (table : ℕ → Fin n → S → ℚ) (h : checkMonitorTable sys M N table = true) (y : Fin n) :
    (∀ σ : BehavioralPolicy sys, traceExpectation sys M σ N 0 (y, []) y (M.initial y) ≤
      (table N y (M.initial y) : ℝ)) ∧
    (∃ σ : BehavioralPolicy sys, traceExpectation sys M σ N 0 (y, []) y (M.initial y) =
      (table N y (M.initial y) : ℝ)) := by
  have hv : value sys M N 0 y (M.initial y) = table N y (M.initial y) := by
    simpa using checked_table_eq_value sys M N table h N le_rfl y (M.initial y)
  rw [← hv]
  exact monitor_optimal_and_attained sys M N y

end Table

end PermanssonResearch.ApplicationBridge.AdaptiveBlockReceipt
