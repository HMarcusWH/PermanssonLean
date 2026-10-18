import PermanssonResearch.ReverseSolver.FlowPolytopeEncoding

namespace PermanssonResearch.ReverseSolver.Occupancy

open ExactPolytope ActionTrace Matrix

variable {C : Type*} [Fintype C] [LinearOrder C] {n N : ℕ}

def rationalInitialRow (μ : Fin n → ℚ) (hμ : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) : Row (Fin n) where
  mass y := (μ y : ℝ)
  nonneg y := by exact_mod_cast hμ y
  total := by exact_mod_cast hμ1

def Flow.vector {sys : TimeSystem C n} {μ : Row (Fin n)} (F : Flow sys μ N) :
    FlowCoordinate C n N → ℝ
  | Sum.inl (t,y) => F.state t y
  | Sum.inr (t,y,c) => F.action t y c

def Flow.terminalValue {sys : TimeSystem C n} {μ : Row (Fin n)} (F : Flow sys μ N)
    (reward : Fin n → ℚ) : ℝ := ∑ y, (reward y : ℝ) * F.state (Fin.last N) y

def flowFromVector (sys : TimeSystem C n) (μ danger : Fin n → ℚ)
    (hμ : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (ρ : ℚ)
    (w : FlowCoordinate C n N → ℝ)
    (hw : w ∈ listFeasible (flowConstraints sys μ danger ρ)) :
    Flow sys (rationalInitialRow μ hμ hμ1) N where
  state t y := w (stateCoordinate t y)
  action t y c := w (actionCoordinate t y c)
  state_nonneg t y := ((flowConstraints_iff sys μ danger ρ w).mp hw).1 _
  action_nonneg t y c := ((flowConstraints_iff sys μ danger ρ w).mp hw).1 _
  initial := ((flowConstraints_iff sys μ danger ρ w).mp hw).2.1
  outflow := ((flowConstraints_iff sys μ danger ρ w).mp hw).2.2.1
  inflow := ((flowConstraints_iff sys μ danger ρ w).mp hw).2.2.2.1
  supported t y c hc := le_antisymm
    (((flowConstraints_iff sys μ danger ρ w).mp hw).2.2.2.2.1 t y c hc)
    (((flowConstraints_iff sys μ danger ρ w).mp hw).1 _)

theorem flowFromVector_risk (sys : TimeSystem C n) (μ danger : Fin n → ℚ)
    (hμ : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (ρ : ℚ)
    (w : FlowCoordinate C n N → ℝ)
    (hw : w ∈ listFeasible (flowConstraints sys μ danger ρ)) :
    (flowFromVector sys μ danger hμ hμ1 ρ w hw).terminalValue danger ≤ (ρ : ℝ) :=
  (flowConstraints_iff sys μ danger ρ w).mp hw |>.2.2.2.2.2

theorem flowFromVector_vector (sys : TimeSystem C n) (μ danger : Fin n → ℚ)
    (hμ : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (ρ : ℚ)
    (w : FlowCoordinate C n N → ℝ)
    (hw : w ∈ listFeasible (flowConstraints sys μ danger ρ)) :
    (flowFromVector sys μ danger hμ hμ1 ρ w hw).vector = w := by
  funext j
  cases j <;> rfl

theorem Flow.vector_feasible {sys : TimeSystem C n} (μ danger : Fin n → ℚ)
    (hμ : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (ρ : ℚ)
    (F : Flow sys (rationalInitialRow μ hμ hμ1) N)
    (hr : F.terminalValue danger ≤ (ρ : ℝ)) :
    F.vector ∈ listFeasible (flowConstraints sys μ danger ρ) := by
  apply (flowConstraints_iff sys μ danger ρ F.vector).mpr
  refine ⟨?_, F.initial, F.outflow, F.inflow, ?_, hr⟩
  · intro j
    rcases j with ⟨t,y⟩ | ⟨t,y,c⟩
    · exact F.state_nonneg t y
    · exact F.action_nonneg t y c
  · intro t y c hc
    exact le_of_eq (F.supported t y c hc)

theorem flowPolytope_bounded (sys : TimeSystem C n) (μ danger : Fin n → ℚ)
    (hμ : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (ρ : ℚ) :
    ∀ w ∈ listFeasible (flowConstraints sys μ danger ρ), (0 : FlowCoordinate C n N → ℝ) ≤ w ∧ w ≤ 1 := by
  intro w hw
  let F := flowFromVector sys μ danger hμ hμ1 ρ w hw
  constructor
  · exact (flowConstraints_iff sys μ danger ρ w).mp hw |>.1
  · intro j
    rcases j with ⟨t,y⟩ | ⟨t,y,c⟩
    · exact F.state_le_one t y
    · exact F.action_le_one t y c

theorem flowPolytope_isCompact (sys : TimeSystem C n) (μ danger : Fin n → ℚ)
    (hμ : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (ρ : ℚ) :
    IsCompact (listFeasible (flowConstraints sys μ danger ρ) : Set (FlowCoordinate C n N → ℝ)) :=
  listFeasible_isCompact _ 0 1 (flowPolytope_bounded sys μ danger hμ hμ1 ρ)

/-- All constraints, candidates and objective comparisons use exact rational arithmetic. -/
def solveRiskFlow (sys : TimeSystem C n) (μ reward danger : Fin n → ℚ) (ρ : ℚ) :
    Option (FlowCoordinate C n N → ℚ) :=
  optimizeList (flowConstraints sys μ danger ρ) (terminalExpression reward)

theorem solveRiskFlow_none_iff (sys : TimeSystem C n) (μ reward danger : Fin n → ℚ)
    (hμ : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (ρ : ℚ) :
    solveRiskFlow (N := N) sys μ reward danger ρ = none ↔
      ¬∃ F : Flow sys (rationalInitialRow μ hμ hμ1) N, F.terminalValue danger ≤ (ρ : ℝ) := by
  rw [solveRiskFlow, optimizeList_none_iff _ _ 0 1 (flowPolytope_bounded sys μ danger hμ hμ1 ρ)]
  constructor
  · intro he ⟨F,hF⟩
    have hf := F.vector_feasible μ danger hμ hμ1 ρ hF
    rw [he] at hf
    exact hf
  · intro hn
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact hn ⟨flowFromVector sys μ danger hμ hμ1 ρ w hw,
      flowFromVector_risk sys μ danger hμ hμ1 ρ w hw⟩

theorem solveRiskFlow_some_optimal (sys : TimeSystem C n) (μ reward danger : Fin n → ℚ)
    (hμ : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (ρ : ℚ)
    (q : FlowCoordinate C n N → ℚ) (hq : solveRiskFlow sys μ reward danger ρ = some q) :
    ∃ F : Flow sys (rationalInitialRow μ hμ hμ1) N,
      F.vector = (fun j => (q j : ℝ)) ∧ F.terminalValue danger ≤ (ρ : ℝ) ∧
      ∀ G : Flow sys (rationalInitialRow μ hμ hμ1) N,
        G.terminalValue danger ≤ (ρ : ℝ) → G.terminalValue reward ≤ F.terminalValue reward := by
  have hqf := optimizeList_some_feasible _ _ q hq
  let F := flowFromVector sys μ danger hμ hμ1 ρ (fun j => (q j : ℝ)) hqf
  refine ⟨F, flowFromVector_vector _ _ _ _ _ _ _ _,
    flowFromVector_risk _ _ _ _ _ _ _ _, ?_⟩
  intro G hG
  have he := optimizeList_some_optimal _ _ q hq 0 1
    (flowPolytope_bounded sys μ danger hμ hμ1 ρ) G.vector
    (G.vector_feasible μ danger hμ hμ1 ρ hG)
  have hcast : (dotProduct (terminalExpression reward) q : ℚ) =
      evaluate (terminalExpression reward) (fun j => (q j : ℝ)) := by
    simp [dotProduct, evaluate]
  rw [hcast, evaluate_terminalExpression] at he
  change evaluate (terminalExpression reward) G.vector ≤ _ at he
  rw [evaluate_terminalExpression] at he
  exact he

end PermanssonResearch.ReverseSolver.Occupancy
