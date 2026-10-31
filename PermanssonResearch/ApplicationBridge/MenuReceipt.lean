import PermanssonResearch.ApplicationBridge.ControlTableReceipt
import PermanssonResearch.ReverseSolver.CanonicalAllHorizonCorrespondence
import Mathlib.Tactic

/-!
# ApplicationBridge — frozen intervention menu receipts

A frozen menu lists finitely many fixed Markov matrices (one per declared
intervention). For a region, start state and horizon, the exit-by-horizon
value of each member is the rational hitting value of the region's complement;
the survival value is its complement. A receipt reports every member's value
and the set of tied optima in the declared direction.

The check is decidable. Soundness identifies each checked value with the
hitting probability in the canonical finite-prefix Markov law
(`rationalHittingValue_eq_canonical_all_horizons`) and the tie set with the
exact set of optimal **listed** members. Nothing is claimed about interventions
outside the menu. With `inducedMatrix` each member is the α/P/U-induced matrix
of a reflected `FiniteWorldInput`; `HeldFixed` records that a member keeps the
baseline's feasible-action relation and world kernel P.
-/

namespace PermanssonResearch.ApplicationBridge.MenuReceipt

open PermanssonResearch.ReverseSolver
open PermanssonResearch.ApplicationBridge.ControlTableReceipt

set_option autoImplicit false

variable {n k : ℕ}

/-- Leaving `region` is hitting its complement; nothing is forbidden. -/
def exitTarget (region : Finset (Fin n)) : RationalHittingTarget n where
  goal := regionᶜ
  forbidden := ∅
  disjoint := Finset.disjoint_empty_right _

/-- Exact objective of one fixed member: exit-by-horizon, or survival. -/
def menuObjective (survival : Bool) (M : RationalMarkovMatrix n)
    (region : Finset (Fin n)) (horizon : ℕ) (start : Fin n) : ℚ :=
  if survival then 1 - rationalHittingValue M (exitTarget region) horizon start
  else rationalHittingValue M (exitTarget region) horizon start

/-- `a` is at least as good as `b` in the declared direction. -/
def atLeastAsGood (maximize : Bool) (a b : ℚ) : Prop :=
  if maximize then b ≤ a else a ≤ b

instance (maximize : Bool) (a b : ℚ) : Decidable (atLeastAsGood maximize a b) := by
  unfold atLeastAsGood
  infer_instance

/-- Reported values are exact and the tie set is exactly the listed optima. -/
def MenuChecks (members : Fin k → RationalMarkovMatrix n) (region : Finset (Fin n))
    (horizon : ℕ) (start : Fin n) (survival maximize : Bool)
    (values : Fin k → ℚ) (tied : Finset (Fin k)) : Prop :=
  (∀ i, values i = menuObjective survival (members i) region horizon start) ∧
  (∀ i, i ∈ tied ↔ ∀ j, atLeastAsGood maximize (values i) (values j)) ∧
  tied.Nonempty

instance (members : Fin k → RationalMarkovMatrix n) (region : Finset (Fin n))
    (horizon : ℕ) (start : Fin n) (survival maximize : Bool)
    (values : Fin k → ℚ) (tied : Finset (Fin k)) :
    Decidable (MenuChecks members region horizon start survival maximize values tied) := by
  unfold MenuChecks
  infer_instance

/-- A false result means the reported values or ties are wrong. -/
def checkMenuReceipt (members : Fin k → RationalMarkovMatrix n) (region : Finset (Fin n))
    (horizon : ℕ) (start : Fin n) (survival maximize : Bool)
    (values : Fin k → ℚ) (tied : Finset (Fin k)) : Bool :=
  decide (MenuChecks members region horizon start survival maximize values tied)

theorem checkMenuReceipt_complete (members : Fin k → RationalMarkovMatrix n)
    (region : Finset (Fin n)) (horizon : ℕ) (start : Fin n) (survival maximize : Bool)
    (values : Fin k → ℚ) (tied : Finset (Fin k))
    (h : checkMenuReceipt members region horizon start survival maximize values tied = true) :
    MenuChecks members region horizon start survival maximize values tied := by
  unfold checkMenuReceipt at h
  exact of_decide_eq_true h

/-- Every checked value is the actual probability of the declared event in
    the canonical finite-prefix Markov law of that member. -/
theorem checked_value_canonical (members : Fin k → RationalMarkovMatrix n)
    (region : Finset (Fin n)) (horizon : ℕ) (start : Fin n) (survival maximize : Bool)
    (values : Fin k → ℚ) (tied : Finset (Fin k))
    (h : checkMenuReceipt members region horizon start survival maximize values tied = true)
    (i : Fin k) :
    (values i : ℝ) =
      if survival then
        1 - hittingValue (rationalTargetAsFrozen (exitTarget region))
          (rationalFiniteKernel (members i)) start horizon
      else
        hittingValue (rationalTargetAsFrozen (exitTarget region))
          (rationalFiniteKernel (members i)) start horizon := by
  rw [(checkMenuReceipt_complete members region horizon start survival maximize
    values tied h).1 i, ← rationalHittingValue_eq_canonical_all_horizons]
  unfold menuObjective
  cases survival <;> simp

/-- The tie set is nonempty and is exactly the set of listed members whose
    exact objective is optimal in the declared direction among listed members. -/
theorem checked_tied_exactly_listed_optima (members : Fin k → RationalMarkovMatrix n)
    (region : Finset (Fin n)) (horizon : ℕ) (start : Fin n) (survival maximize : Bool)
    (values : Fin k → ℚ) (tied : Finset (Fin k))
    (h : checkMenuReceipt members region horizon start survival maximize values tied = true) :
    tied.Nonempty ∧
    ∀ i, i ∈ tied ↔ ∀ j, atLeastAsGood maximize
      (menuObjective survival (members i) region horizon start)
      (menuObjective survival (members j) region horizon start) := by
  obtain ⟨hval, htied, hne⟩ :=
    checkMenuReceipt_complete members region horizon start survival maximize values tied h
  refine ⟨hne, fun i => ?_⟩
  rw [htied i]
  simp only [hval]

/-- The exact objective of any fixed matrix is the actual canonical-law
    probability of the declared event (or its complement for survival). -/
theorem menuObjective_canonical (survival : Bool) (M : RationalMarkovMatrix n)
    (region : Finset (Fin n)) (horizon : ℕ) (start : Fin n) :
    (menuObjective survival M region horizon start : ℝ) =
      if survival then
        1 - hittingValue (rationalTargetAsFrozen (exitTarget region))
          (rationalFiniteKernel M) start horizon
      else
        hittingValue (rationalTargetAsFrozen (exitTarget region))
          (rationalFiniteKernel M) start horizon := by
  rw [← rationalHittingValue_eq_canonical_all_horizons]
  unfold menuObjective
  cases survival <;> simp

/-! ## Killed-kernel survival tables -/

/-- A complete survival table: entry `t y` is the probability of staying in
    `region` at observation times `0..t` from `y`, for every `t ≤ horizon`. -/
def SurvivalTableChecks (M : RationalMarkovMatrix n) (region : Finset (Fin n))
    (horizon : ℕ) (table : ℕ → Fin n → ℚ) : Prop :=
  ∀ t : Fin (horizon + 1), ∀ y : Fin n,
    table t.val y = menuObjective true M region t.val y

instance (M : RationalMarkovMatrix n) (region : Finset (Fin n)) (horizon : ℕ)
    (table : ℕ → Fin n → ℚ) : Decidable (SurvivalTableChecks M region horizon table) := by
  unfold SurvivalTableChecks
  infer_instance

def checkSurvivalTable (M : RationalMarkovMatrix n) (region : Finset (Fin n))
    (horizon : ℕ) (table : ℕ → Fin n → ℚ) : Bool :=
  decide (SurvivalTableChecks M region horizon table)

/-- Every checked entry is one minus the canonical-law probability of having
    left `region` by that time. -/
theorem checked_survival_table_canonical (M : RationalMarkovMatrix n)
    (region : Finset (Fin n)) (horizon : ℕ) (table : ℕ → Fin n → ℚ)
    (h : checkSurvivalTable M region horizon table = true)
    (t : ℕ) (ht : t ≤ horizon) (y : Fin n) :
    (table t y : ℝ) =
      1 - hittingValue (rationalTargetAsFrozen (exitTarget region))
        (rationalFiniteKernel M) y t := by
  unfold checkSurvivalTable at h
  have hentry := of_decide_eq_true h ⟨t, Nat.lt_succ_of_le ht⟩ y
  simp only at hentry
  rw [hentry, menuObjective_canonical]
  simp

/-- A listed member keeps the baseline's feasible-action relation and world
    kernel P; only α and U may differ. -/
def HeldFixed {ns nx na : ℕ} (base w : FiniteWorldInput ns nx na) : Prop :=
  (∀ s x a, w.feasible s x a ↔ base.feasible s x a) ∧
  ∀ s x a xp, w.world s x a xp = base.world s x a xp

end PermanssonResearch.ApplicationBridge.MenuReceipt
