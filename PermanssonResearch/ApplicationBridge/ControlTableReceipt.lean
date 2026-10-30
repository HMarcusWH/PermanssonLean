import PermanssonResearch.ApplicationBridge.FiniteWorldInput
import PermanssonResearch.ReverseSolver.BellmanOptimality
import Mathlib.Tactic

/-!
# ApplicationBridge — bounded exact Bellman table certificates

A complete finite rational value/choice table is checked against the actual
FiniteControlSystem, its admitted controls, and the original hitting target.
The checker is finite (Fin N), not a search for a presumed optimum.
Soundness transports the checked values to the existing Bellman theorem.

A FiniteControlSystem must itself be bound to source-model P/U kernels before
this proves anything about an externally submitted alpha/P/U application.
No empirical identification, original-regime certification, or release
approval follows from this module alone.
-/

namespace PermanssonResearch.ApplicationBridge.ControlTableReceipt

open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.ControlledKernel
open PermanssonResearch.ReverseSolver.Bellman

set_option autoImplicit false

variable {m n : ℕ}

/-- Full finite receipt obligations. The reported table uses t transitions
    remaining; chosen t is applied with t+1 remaining.
    Terminal states need not have winning actions, but selected controls are
    always admitted. All ties are permitted when their scores are maximal. -/
def TableChecks (sys : FiniteControlSystem (Fin m) n)
    (target : RationalHittingTarget n) (N : ℕ)
    (values : ℕ → Fin n → ℚ) (chosen : ℕ → Fin n → Fin m) : Prop :=
  (∀ y : Fin n, values 0 y = if y ∈ target.goal then 1 else 0) ∧
  (∀ t : Fin N, ∀ y : Fin n,
    values (t.val + 1) y =
      if y ∈ target.goal then 1
      else if y ∈ target.forbidden then 0
      else actionScore sys (values t.val) y (chosen t.val y)) ∧
  (∀ t : Fin N, ∀ y : Fin n, chosen t.val y ∈ sys.options y) ∧
  (∀ t : Fin N, ∀ y : Fin n,
    y ∉ target.goal → y ∉ target.forbidden →
      ∀ c : Fin m, c ∈ sys.options y →
        actionScore sys (values t.val) y c ≤
          actionScore sys (values t.val) y (chosen t.val y))

/-- Every obligation quantifies over Fin types, Finset membership and exact
    rational (in)equalities, so the full table check is decidable. -/
instance (sys : FiniteControlSystem (Fin m) n)
    (target : RationalHittingTarget n) (N : ℕ)
    (values : ℕ → Fin n → ℚ) (chosen : ℕ → Fin n → Fin m) :
    Decidable (TableChecks sys target N values chosen) := by
  unfold TableChecks
  infer_instance

/-- Executable on finite rational data. A false result is not evidence of
    infeasibility: it means the supplied table fails these obligations. -/
def checkBellmanReceipt (sys : FiniteControlSystem (Fin m) n)
    (target : RationalHittingTarget n) (N : ℕ)
    (values : ℕ → Fin n → ℚ) (chosen : ℕ → Fin n → Fin m) : Bool :=
  decide (TableChecks sys target N values chosen)

/-- A successful Boolean check produces the entire proof obligation,
    not a caller-owned assertion that the receipt was accepted. -/
theorem checkBellmanReceipt_complete
    (sys : FiniteControlSystem (Fin m) n)
    (target : RationalHittingTarget n) (N : ℕ)
    (values : ℕ → Fin n → ℚ) (chosen : ℕ → Fin n → Fin m)
    (h : checkBellmanReceipt sys target N values chosen = true) :
    TableChecks sys target N values chosen := by
  unfold checkBellmanReceipt at h
  exact of_decide_eq_true h

/-- Exact recurrence plus complete action comparison yields the original
    Bellman value for every state and every declared horizon. -/
theorem checked_table_eq_bellman
    (sys : FiniteControlSystem (Fin m) n)
    (target : RationalHittingTarget n) (N : ℕ)
    (values : ℕ → Fin n → ℚ) (chosen : ℕ → Fin n → Fin m)
    (h : TableChecks sys target N values chosen) :
    ∀ t : ℕ, t ≤ N → ∀ y : Fin n,
      values t y = bellmanValue sys target t y := by
  rcases h with ⟨hzero, hstep, hpermitted, hmax⟩
  intro t
  induction t with
  | zero =>
      intro _ y
      simpa only [bellmanValue_zero] using hzero y
  | succ t ih =>
      intro hle y
      have ht : t < N := Nat.lt_of_succ_le hle
      rw [hstep (⟨t, ht⟩ : Fin N) y, bellmanValue_succ]
      by_cases hg : y ∈ target.goal
      · simp [hg]
      · simp only [hg, ↓reduceIte]
        by_cases hd : y ∈ target.forbidden
        · simp [hd]
        · simp only [hd, ↓reduceIte]
          have hprev : values t = bellmanValue sys target t := by
            funext z
            exact ih (Nat.le_of_lt ht) z
          rw [hprev]
          apply le_antisymm
          · exact bestControl_dominates sys (bellmanValue sys target t) y
              (chosen t y) (hpermitted (⟨t, ht⟩ : Fin N) y)
          · have hbest := hmax (⟨t, ht⟩ : Fin N) y hg hd
                (bestControl sys (bellmanValue sys target t) y)
                (bestControl_mem sys (bellmanValue sys target t) y)
            simpa only [hprev] using hbest

/-- Successful checking identifies the Bellman value and thus bounds every
    admitted remaining-horizon Markov schedule; one schedule attains it.
    No identity with an arbitrary tied solver-selected vector is assumed. -/
theorem checkBellmanReceipt_sound
    (sys : FiniteControlSystem (Fin m) n)
    (target : RationalHittingTarget n) (N : ℕ)
    (values : ℕ → Fin n → ℚ) (chosen : ℕ → Fin n → Fin m)
    (h : checkBellmanReceipt sys target N values chosen = true) :
    (∀ y : Fin n, values N y = bellmanValue sys target N y) ∧
    (∀ (π : MarkovSchedule sys) (y : Fin n),
      policyValue sys target π N y ≤ values N y) ∧
    (∃ π : MarkovSchedule sys, ∀ y : Fin n,
      policyValue sys target π N y = values N y) := by
  have heq := checked_table_eq_bellman sys target N values chosen
    (checkBellmanReceipt_complete sys target N values chosen h)
  refine ⟨fun y => heq N (Nat.le_refl N) y, ?_, ?_⟩
  · intro π y
    rw [heq N (Nat.le_refl N) y]
    exact policyValue_le_bellman sys target π N y
  · refine ⟨maximizingSchedule sys target, ?_⟩
    intro y
    rw [heq N (Nat.le_refl N) y]
    exact maximizingSchedule_attains sys target N y

/-- The selected receipt action is admitted and locally maximal at every
    nonterminal state, even in the presence of tied maxima. -/
theorem checkBellmanReceipt_selected
    (sys : FiniteControlSystem (Fin m) n)
    (target : RationalHittingTarget n) (N : ℕ)
    (values : ℕ → Fin n → ℚ) (chosen : ℕ → Fin n → Fin m)
    (h : checkBellmanReceipt sys target N values chosen = true)
    (t : Fin N) (y : Fin n)
    (hg : y ∉ target.goal) (hd : y ∉ target.forbidden) :
    chosen t.val y ∈ sys.options y ∧
    ∀ c : Fin m, c ∈ sys.options y →
      actionScore sys (values t.val) y c ≤
        actionScore sys (values t.val) y (chosen t.val y) := by
  rcases checkBellmanReceipt_complete sys target N values chosen h with
    ⟨_, _, hp, hm⟩
  exact ⟨hp t y, hm t y hg hd⟩

/-! ## Binding the control system to a finite α/P/U source

The theorems above hold for any `FiniteControlSystem`. The construction below
removes the remaining gap for application inputs: controls are the source
action indices, the matrix of control `a` is the fixed-action `P·U` row of a
`FiniteWorldInput`, and the admitted controls at each joint state are exactly
the source's feasible actions. Joint states use the application's declared
order `(s, x) ↦ s * nx + x`. -/

section FiniteWorldBinding

open PermanssonResearch.ApplicationBridge

variable {ns nx na : ℕ}

/-- The application's joint-state order `(s, x) ↦ s * nx + x`. -/
abbrev jointIndex : Fin ns × Fin nx ≃ Fin (ns * nx) := finProdFinEquiv

/-- Fixed-action `P·U` rows of the source, as a Markov matrix on joint
    indices. Row normalization is the source primitive proof, transported
    along the joint-state order. -/
def controlledMatrix (w : FiniteWorldInput ns nx na) (a : Fin na) :
    RationalMarkovMatrix (ns * nx) where
  entry := fun y z => w.controlledAtom a (jointIndex.symm y) (jointIndex.symm z)
  entry_nonneg := fun y z => w.controlledAtom_nonneg a _ _
  row_sum_one := by
    intro y
    rw [← w.controlledAtom_sum_one a (jointIndex.symm y)]
    exact Fintype.sum_equiv jointIndex.symm _ _ (fun _ => rfl)

/-- The source's α/P/U-induced (uncontrolled baseline) matrix. -/
def inducedMatrix (w : FiniteWorldInput ns nx na) :
    RationalMarkovMatrix (ns * nx) where
  entry := fun y z => w.inducedAtom (jointIndex.symm y) (jointIndex.symm z)
  entry_nonneg := fun y z => w.inducedAtom_nonneg _ _
  row_sum_one := by
    intro y
    rw [← w.inducedAtom_sum_one (jointIndex.symm y)]
    exact Fintype.sum_equiv jointIndex.symm _ _ (fun _ => rfl)

/-- Admitted controls are exactly the source's feasible actions. -/
def AdmittedExactly (w : FiniteWorldInput ns nx na)
    (options : Fin (ns * nx) → Finset (Fin na)) : Prop :=
  ∀ y a, a ∈ options y ↔
    w.feasible (jointIndex.symm y).1 (jointIndex.symm y).2 a

/-- Every source state has a feasible action: α is a probability vector that
    vanishes on infeasible actions. No separate nonemptiness claim is trusted. -/
theorem options_nonempty_of_exact (w : FiniteWorldInput ns nx na)
    (options : Fin (ns * nx) → Finset (Fin na))
    (hexact : AdmittedExactly w options) (y : Fin (ns * nx)) :
    (options y).Nonempty := by
  by_contra hempty
  have hzero : ∀ a, w.alpha (jointIndex.symm y).1 (jointIndex.symm y).2 a = 0 := by
    intro a
    apply w.alpha_zero_of_infeasible
    intro hfeas
    exact hempty ⟨a, (hexact y a).mpr hfeas⟩
  have hsum := w.alpha_sum_one (jointIndex.symm y).1 (jointIndex.symm y).2
  simp only [hzero, Finset.sum_const_zero] at hsum
  exact zero_ne_one hsum

/-- The fully observed control system determined by the source α/P/U input
    and its feasible-action relation. -/
def boundControlSystem (w : FiniteWorldInput ns nx na)
    (options : Fin (ns * nx) → Finset (Fin na))
    (hexact : AdmittedExactly w options) (hpos : 0 < ns * nx) :
    FiniteControlSystem (Fin na) (ns * nx) where
  states_nonempty := hpos
  baseline := inducedMatrix w
  options := options
  options_nonempty := options_nonempty_of_exact w options hexact
  matrix := controlledMatrix w

/-- Action scores of the bound system are the source primitive sums over the
    joint destination, not a separately supplied numeric matrix. -/
theorem bound_actionScore_eq_primitives (w : FiniteWorldInput ns nx na)
    (options : Fin (ns * nx) → Finset (Fin na))
    (hexact : AdmittedExactly w options) (hpos : 0 < ns * nx)
    (v : Fin (ns * nx) → ℚ) (y : Fin (ns * nx)) (a : Fin na) :
    actionScore (boundControlSystem w options hexact hpos) v y a =
      ∑ z : Fin ns × Fin nx,
        w.world (jointIndex.symm y).1 (jointIndex.symm y).2 a z.2 *
          w.update (jointIndex.symm y).1 (jointIndex.symm y).2 a z.2 z.1 *
            v (jointIndex z) := by
  unfold actionScore
  refine Fintype.sum_equiv jointIndex.symm _ _ (fun z => ?_)
  rw [Equiv.apply_symm_apply]
  rfl

/-- A checked table for the source-bound system yields the Bellman value of
    the source α/P/U control problem, the upper bound for every admitted
    remaining-horizon Markov schedule and its attainment, and source
    feasibility of every selected action. -/
theorem checkBellmanReceipt_sound_of_finite_world
    (w : FiniteWorldInput ns nx na)
    (options : Fin (ns * nx) → Finset (Fin na))
    (hexact : AdmittedExactly w options) (hpos : 0 < ns * nx)
    (target : RationalHittingTarget (ns * nx)) (N : ℕ)
    (values : ℕ → Fin (ns * nx) → ℚ) (chosen : ℕ → Fin (ns * nx) → Fin na)
    (h : checkBellmanReceipt (boundControlSystem w options hexact hpos)
      target N values chosen = true) :
    (∀ y, values N y =
      bellmanValue (boundControlSystem w options hexact hpos) target N y) ∧
    (∀ (π : MarkovSchedule (boundControlSystem w options hexact hpos)) y,
      policyValue (boundControlSystem w options hexact hpos) target π N y ≤
        values N y) ∧
    (∃ π : MarkovSchedule (boundControlSystem w options hexact hpos), ∀ y,
      policyValue (boundControlSystem w options hexact hpos) target π N y =
        values N y) ∧
    (∀ (t : Fin N) (y : Fin (ns * nx)),
      w.feasible (jointIndex.symm y).1 (jointIndex.symm y).2 (chosen t.val y)) := by
  refine ⟨(checkBellmanReceipt_sound _ target N values chosen h).1,
    (checkBellmanReceipt_sound _ target N values chosen h).2.1,
    (checkBellmanReceipt_sound _ target N values chosen h).2.2, ?_⟩
  intro t y
  rcases checkBellmanReceipt_complete _ target N values chosen h with
    ⟨_, _, hp, _⟩
  exact (hexact y (chosen t.val y)).mp (hp t y)

end FiniteWorldBinding

end PermanssonResearch.ApplicationBridge.ControlTableReceipt
