import PermanssonResearch.ReverseSolver.FlowExpressions
import PermanssonResearch.ReverseSolver.FiniteOccupancyModel

namespace PermanssonResearch.ReverseSolver.Occupancy

open ExactPolytope ActionTrace

variable {C : Type*} [Fintype C] [LinearOrder C] {n N : ℕ}

abbrev FlowCoordinate (C : Type*) (n N : ℕ) :=
  (Fin (N+1) × Fin n) ⊕ (Fin N × Fin n × C)

def stateCoordinate (t : Fin (N+1)) (y : Fin n) : FlowCoordinate C n N := Sum.inl (t,y)
def actionCoordinate (t : Fin N) (y : Fin n) (c : C) : FlowCoordinate C n N := Sum.inr (t,y,c)

def stateExpression (t : Fin (N+1)) (y : Fin n) : FlowCoordinate C n N → ℚ :=
  coordinate (stateCoordinate t y)

def actionExpression (t : Fin N) (y : Fin n) (c : C) : FlowCoordinate C n N → ℚ :=
  coordinate (actionCoordinate t y c)

def outflowExpression (t : Fin N) (y : Fin n) : FlowCoordinate C n N → ℚ :=
  (∑ c : C, actionExpression t y c) - stateExpression t.castSucc y

def inflowExpression (sys : TimeSystem C n) (t : Fin N) (z : Fin n) :
    FlowCoordinate C n N → ℚ :=
  stateExpression t.succ z -
    ∑ y : Fin n, ∑ c : C, (sys.matrix t.val c).entry y z • actionExpression t y c

def terminalExpression (reward : Fin n → ℚ) : FlowCoordinate C n N → ℚ :=
  ∑ y : Fin n, reward y • stateExpression (Fin.last N) y

@[simp] theorem evaluate_stateExpression (w : FlowCoordinate C n N → ℝ)
    (t : Fin (N+1)) (y : Fin n) : evaluate (stateExpression t y) w = w (stateCoordinate t y) :=
  evaluate_coordinate _ w

@[simp] theorem evaluate_actionExpression (w : FlowCoordinate C n N → ℝ)
    (t : Fin N) (y : Fin n) (c : C) : evaluate (actionExpression t y c) w = w (actionCoordinate t y c) :=
  evaluate_coordinate _ w

@[simp] theorem evaluate_outflowExpression (w : FlowCoordinate C n N → ℝ)
    (t : Fin N) (y : Fin n) : evaluate (outflowExpression t y) w =
      (∑ c : C, w (actionCoordinate t y c)) - w (stateCoordinate t.castSucc y) := by
  simp [outflowExpression]

@[simp] theorem evaluate_inflowExpression (sys : TimeSystem C n)
    (w : FlowCoordinate C n N → ℝ) (t : Fin N) (z : Fin n) :
    evaluate (inflowExpression sys t z) w = w (stateCoordinate t.succ z) -
      ∑ y : Fin n, ∑ c : C, ((sys.matrix t.val c).entry y z : ℝ) * w (actionCoordinate t y c) := by
  simp [inflowExpression]

@[simp] theorem evaluate_terminalExpression (reward : Fin n → ℚ)
    (w : FlowCoordinate C n N → ℝ) : evaluate (terminalExpression reward) w =
      ∑ y : Fin n, (reward y : ℝ) * w (stateCoordinate (Fin.last N) y) := by
  simp [terminalExpression]

def coordinateList (C : Type*) [Fintype C] [LinearOrder C] (n N : ℕ) : List (FlowCoordinate C n N) :=
  (((List.finRange (N+1)).product (List.finRange n)).map Sum.inl) ++
  (((List.finRange N).product ((List.finRange n).product (Finset.univ.sort (· ≤ ·)))).map Sum.inr)

theorem mem_coordinateList (j : FlowCoordinate C n N) : j ∈ coordinateList C n N := by
  rcases j with ⟨t,y⟩ | ⟨t,y,c⟩ <;> simp [coordinateList]

theorem forall_timeState (P : Fin N × Fin n → Prop) :
    (∀ p ∈ (List.finRange N).product (List.finRange n), P p) ↔ ∀ t y, P (t,y) := by
  constructor
  · intro h t y
    exact h (t,y) (by simp)
  · intro h p _
    exact h p.1 p.2

theorem forall_timeStateControl (P : Fin N × Fin n × C → Prop) :
    (∀ p ∈ (List.finRange N).product ((List.finRange n).product (Finset.univ.sort (· ≤ ·))), P p) ↔
      ∀ t y c, P (t,y,c) := by
  constructor
  · intro h t y c
    exact h (t,y,c) (by simp)
  · intro h p _
    exact h p.1 p.2.1 p.2.2

def initialConstraints (μ : Fin n → ℚ) : List (RationalConstraint (FlowCoordinate C n N)) :=
  (List.finRange n).flatMap fun y => equalityConstraints (stateExpression 0 y) (μ y)

def outflowConstraints : List (RationalConstraint (FlowCoordinate C n N)) :=
  ((List.finRange N).product (List.finRange n)).flatMap fun p =>
    equalityConstraints (outflowExpression p.1 p.2) 0

def inflowConstraints (sys : TimeSystem C n) : List (RationalConstraint (FlowCoordinate C n N)) :=
  ((List.finRange N).product (List.finRange n)).flatMap fun p =>
    equalityConstraints (inflowExpression sys p.1 p.2) 0

def nonnegativeConstraints : List (RationalConstraint (FlowCoordinate C n N)) :=
  (coordinateList C n N).map fun j => ⟨-coordinate j,0⟩

def supportConstraints (sys : TimeSystem C n) : List (RationalConstraint (FlowCoordinate C n N)) :=
  ((List.finRange N).product ((List.finRange n).product (Finset.univ.sort (· ≤ ·)))).map fun p =>
    ⟨if p.2.2 ∈ sys.options p.1.val p.2.1 then 0 else actionExpression p.1 p.2.1 p.2.2,0⟩

def flowConstraints (sys : TimeSystem C n) (μ danger : Fin n → ℚ) (ρ : ℚ) :
    List (RationalConstraint (FlowCoordinate C n N)) :=
  nonnegativeConstraints ++ initialConstraints μ ++ outflowConstraints ++
    inflowConstraints sys ++ supportConstraints sys ++ [⟨terminalExpression danger,ρ⟩]

theorem nonnegativeConstraints_iff (w : FlowCoordinate C n N → ℝ) :
    (∀ a ∈ nonnegativeConstraints, a.holds w) ↔ ∀ j, 0 ≤ w j := by
  simp only [nonnegativeConstraints, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  simp only [constraint_holds, evaluate_neg, evaluate_coordinate,
    Rat.cast_zero, neg_nonpos]
  exact ⟨fun h j => h j (mem_coordinateList j), fun h j _ => h j⟩

theorem initialConstraints_iff (μ : Fin n → ℚ) (w : FlowCoordinate C n N → ℝ) :
    (∀ a ∈ initialConstraints μ, a.holds w) ↔
      ∀ y, w (stateCoordinate 0 y) = (μ y : ℝ) := by
  simp only [initialConstraints, List.forall_mem_flatMap, List.mem_finRange,
    forall_const, equalityConstraints_iff, evaluate_stateExpression]

theorem outflowConstraints_iff (w : FlowCoordinate C n N → ℝ) :
    (∀ a ∈ outflowConstraints, a.holds w) ↔
      ∀ t y, (∑ c : C, w (actionCoordinate t y c)) = w (stateCoordinate t.castSucc y) := by
  simp only [outflowConstraints, List.forall_mem_flatMap, forall_timeState,
    equalityConstraints_iff, evaluate_outflowExpression, Rat.cast_zero, sub_eq_zero]

theorem inflowConstraints_iff (sys : TimeSystem C n) (w : FlowCoordinate C n N → ℝ) :
    (∀ a ∈ inflowConstraints sys, a.holds w) ↔
      ∀ t z, w (stateCoordinate t.succ z) =
        ∑ y : Fin n, ∑ c : C, w (actionCoordinate t y c) * ((sys.matrix t.val c).entry y z : ℝ) := by
  simp only [inflowConstraints, List.forall_mem_flatMap, forall_timeState,
    equalityConstraints_iff, evaluate_inflowExpression, Rat.cast_zero, sub_eq_zero]
  simp only [mul_comm]

theorem supportConstraints_iff (sys : TimeSystem C n) (w : FlowCoordinate C n N → ℝ) :
    (∀ a ∈ supportConstraints sys, a.holds w) ↔
      ∀ t y c, c ∉ sys.options t.val y → w (actionCoordinate t y c) ≤ 0 := by
  have he : (∀ a ∈ supportConstraints sys, a.holds w) ↔
      ∀ t y c, evaluate
        (if c ∈ sys.options t.val y then 0 else actionExpression t y c) w ≤ 0 := by
    simp only [supportConstraints, List.forall_mem_map, forall_timeStateControl,
      constraint_holds, Rat.cast_zero]
  rw [he]
  constructor
  · intro h t y c hc
    simpa [hc] using h t y c
  · intro h t y c
    by_cases hc : c ∈ sys.options t.val y
    · simp [hc]
    · simpa [hc] using h t y c hc

theorem flowConstraints_iff (sys : TimeSystem C n) (μ danger : Fin n → ℚ) (ρ : ℚ)
    (w : FlowCoordinate C n N → ℝ) :
    w ∈ listFeasible (flowConstraints sys μ danger ρ) ↔
      (∀ j, 0 ≤ w j) ∧
      (∀ y, w (stateCoordinate 0 y) = (μ y : ℝ)) ∧
      (∀ t y, (∑ c : C, w (actionCoordinate t y c)) = w (stateCoordinate t.castSucc y)) ∧
      (∀ t z, w (stateCoordinate t.succ z) =
        ∑ y : Fin n, ∑ c : C, w (actionCoordinate t y c) * ((sys.matrix t.val c).entry y z : ℝ)) ∧
      (∀ t y c, c ∉ sys.options t.val y → w (actionCoordinate t y c) ≤ 0) ∧
      (∑ y : Fin n, (danger y : ℝ) * w (stateCoordinate (Fin.last N) y)) ≤ (ρ : ℝ) := by
  simp only [listFeasible, Set.mem_setOf_eq, flowConstraints, List.forall_mem_append,
    List.forall_mem_singleton]
  rw [nonnegativeConstraints_iff, initialConstraints_iff, outflowConstraints_iff,
    inflowConstraints_iff, supportConstraints_iff]
  simp only [constraint_holds, evaluate_terminalExpression, and_assoc]

end PermanssonResearch.ReverseSolver.Occupancy
