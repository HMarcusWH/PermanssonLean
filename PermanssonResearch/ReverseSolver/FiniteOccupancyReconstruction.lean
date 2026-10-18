import PermanssonResearch.ReverseSolver.FiniteOccupancyHistory

/-! Every real feasible flow is realized by the legal x/d controller, with
exact actual state/action marginals and all terminal expectations at once. -/

namespace PermanssonResearch.ReverseSolver.Occupancy
open ControlledKernel ActionTrace MeasureTheory
noncomputable section
variable {C : Type*} [Fintype C] [DecidableEq C] {n N : ℕ}
variable {sys : TimeSystem C n} {μ : Row (Fin n)}

theorem actionMass_policy (F : Flow sys μ N) (t : ℕ) (y : Fin n) (c : C) :
    actionMass sys F.policy μ t y c=
      stateMass sys F.policy μ t y*(F.markovControl t y).mass c := by
  rw [actionMass_eq_expect,stateMass_eq_expect,← expect_mul_const]
  congr 1
  funext h
  by_cases hy : last t h=y <;> simp [Flow.policy,hy]

theorem stateMass_policy_eq (F : Flow sys μ N) :
    ∀ t : Fin (N+1), ∀ y : Fin n, stateMass sys F.policy μ t.val y=F.state t y := by
  intro t
  refine Fin.induction ?_ ?_ t
  · intro y
    change stateMass sys F.policy μ 0 y=F.state 0 y
    rw [stateMass_initial,F.initial]
  · intro k ih z
    change stateMass sys F.policy μ (k.val+1) z=F.state k.succ z
    change ∀ y, stateMass sys F.policy μ k.val y=F.state k.castSucc y at ih
    rw [stateMass_inflow,F.inflow]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro c _
    rw [actionMass_policy,ih y,F.state_mul_markovControl]

theorem actionMass_policy_eq (F : Flow sys μ N) (t : Fin N) (y : Fin n) (c : C) :
    actionMass sys F.policy μ t.val y c=F.action t y c := by
  have hs : stateMass sys F.policy μ t.val y=F.state t.castSucc y := stateMass_policy_eq F t.castSucc y
  rw [actionMass_policy,hs,F.state_mul_markovControl]

theorem policy_realizes_flow (F : Flow sys μ N) :
    (∀ t y, (occupancies sys F.policy μ N).state t y=F.state t y) ∧
    (∀ t y c, (occupancies sys F.policy μ N).action t y c=F.action t y c) :=
  ⟨stateMass_policy_eq F,actionMass_policy_eq F⟩

theorem reconstructed_terminal_expectation (F : Flow sys μ N) (R : Fin n → ℝ) :
    (historyLaw sys F.policy μ N).expect (fun h => R (last N h))=
      ∑ y : Fin n, F.state (Fin.last N) y*R y := by
  rw [terminal_expect_eq_occupancy]
  apply Finset.sum_congr rfl
  intro y _
  rw [(policy_realizes_flow F).1]

theorem reconstructed_actual_terminal_integral (F : Flow sys μ N) (R : Fin n → ℝ) :
    (∫ h, R (last N h) ∂actualHistoryMeasure sys F.policy μ N)=
      ∑ y : Fin n, F.state (Fin.last N) y*R y := by
  rw [actual_terminal_integral_eq_occupancy]
  apply Finset.sum_congr rfl
  intro y _
  rw [(policy_realizes_flow F).1]

/-- The controller and its exact marginals are chosen independently of the
terminal score; success and hard-risk scores therefore hold simultaneously. -/
theorem exists_policy_realizing_flow (F : Flow sys μ N) :
    ∃ σ : BehavioralPolicy sys,
      (∀ t y, (occupancies sys σ μ N).state t y=F.state t y) ∧
      (∀ t y c, (occupancies sys σ μ N).action t y c=F.action t y c) ∧
      (∀ R : Fin n → ℝ, (∫ h, R (last N h) ∂actualHistoryMeasure sys σ μ N)=
        ∑ y : Fin n, F.state (Fin.last N) y*R y) :=
  ⟨F.policy,(policy_realizes_flow F).1,(policy_realizes_flow F).2,
    reconstructed_actual_terminal_integral F⟩

/-- Actual all-history/flow equivalence, on the same real terminal scores.
The feasible-flow-to-policy direction supplies a concrete legal controller. -/
theorem actual_history_flow_equivalence (sys : TimeSystem C n) (μ : Row (Fin n)) (N : ℕ) :
    (∀ σ : BehavioralPolicy sys, ∃ F : Flow sys μ N,
      ∀ R : Fin n → ℝ, (∫ h, R (last N h) ∂actualHistoryMeasure sys σ μ N)=
        ∑ y : Fin n, F.state (Fin.last N) y*R y) ∧
    (∀ F : Flow sys μ N, ∃ σ : BehavioralPolicy sys,
      ∀ R : Fin n → ℝ, (∫ h, R (last N h) ∂actualHistoryMeasure sys σ μ N)=
        ∑ y : Fin n, F.state (Fin.last N) y*R y) := by
  constructor
  · intro σ
    exact ⟨occupancies sys σ μ N,actual_terminal_integral_eq_occupancy sys σ μ N⟩
  · intro F
    exact ⟨F.policy,reconstructed_actual_terminal_integral F⟩

def actualTerminalScore (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (N : ℕ) (R : Fin n → ℝ) : ℝ :=
  ∫ h, R (last N h) ∂actualHistoryMeasure sys σ μ N

def flowTerminalScore (F : Flow sys μ N) (R : Fin n → ℝ) : ℝ :=
  ∑ y : Fin n, F.state (Fin.last N) y*R y

/-- The attainable success/risk pairs agree exactly. This is the interface
needed by a hard-risk LP, where success and danger are separate scores. -/
theorem actual_success_risk_range_eq_flow (sys : TimeSystem C n) (μ : Row (Fin n))
    (N : ℕ) (R D : Fin n → ℝ) :
    Set.range (fun σ : BehavioralPolicy sys =>
      (actualTerminalScore sys σ μ N R,actualTerminalScore sys σ μ N D))=
    Set.range (fun F : Flow sys μ N => (flowTerminalScore F R,flowTerminalScore F D)) := by
  apply Set.Subset.antisymm
  · rintro p ⟨σ,rfl⟩
    refine ⟨occupancies sys σ μ N,?_⟩
    apply Prod.ext
    · exact (actual_terminal_integral_eq_occupancy sys σ μ N R).symm
    · exact (actual_terminal_integral_eq_occupancy sys σ μ N D).symm
  · rintro p ⟨F,rfl⟩
    refine ⟨F.policy,?_⟩
    apply Prod.ext
    · exact reconstructed_actual_terminal_integral F R
    · exact reconstructed_actual_terminal_integral F D

end
end PermanssonResearch.ReverseSolver.Occupancy
