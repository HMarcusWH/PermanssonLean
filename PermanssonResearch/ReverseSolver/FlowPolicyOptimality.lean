import PermanssonResearch.ReverseSolver.FlowPolytope
import PermanssonResearch.ReverseSolver.FiniteOccupancyReconstruction

/-!
# Exact hard-risk optimization over all actual randomized histories

Success and danger are evaluated under the same normalized chronological law.
The solver returns an infeasibility result or a rational flow whose legal x/d
controller attains the optimum over every allowed real behavioral history rule.
-/

namespace PermanssonResearch.ReverseSolver.Occupancy

open ExactPolytope ActionTrace Matrix

variable {C : Type*} [Fintype C] [LinearOrder C] {n N : ℕ}

theorem actualTerminalScore_eq_flowValue (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (N : ℕ) (R : Fin n → ℚ) :
    actualTerminalScore sys σ μ N (fun y => (R y : ℝ)) =
      (occupancies sys σ μ N).terminalValue R := by
  simpa only [actualTerminalScore, Flow.terminalValue, mul_comm] using
    actual_terminal_integral_eq_occupancy sys σ μ N (fun y => (R y : ℝ))

theorem actualTerminalScore_reconstructed {sys : TimeSystem C n} {μ : Row (Fin n)}
    (F : Flow sys μ N) (R : Fin n → ℚ) :
    actualTerminalScore sys F.policy μ N (fun y => (R y : ℝ)) = F.terminalValue R := by
  simpa only [actualTerminalScore, Flow.terminalValue, mul_comm] using
    reconstructed_actual_terminal_integral F (fun y => (R y : ℝ))

theorem Flow.vector_policy {sys : TimeSystem C n} {μ : Row (Fin n)} (F : Flow sys μ N) :
    (occupancies sys F.policy μ N).vector = F.vector := by
  funext j
  rcases j with ⟨t,y⟩ | ⟨t,y,c⟩
  · exact (policy_realizes_flow F).1 t y
  · exact (policy_realizes_flow F).2 t y c

theorem Flow.terminalValue_eq_evaluate {sys : TimeSystem C n} {μ : Row (Fin n)}
    (F : Flow sys μ N) (R : Fin n → ℚ) :
    F.terminalValue R = evaluate (terminalExpression R) F.vector := by
  simp only [Flow.terminalValue, evaluate_terminalExpression, Flow.vector, stateCoordinate]

/-- Infeasibility covers every real nonanticipating full-history controller. -/
theorem solveRiskFlow_none_iff_no_behavioral_policy (sys : TimeSystem C n)
    (μ reward danger : Fin n → ℚ) (hμ : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (ρ : ℚ) :
    solveRiskFlow (N := N) sys μ reward danger ρ = none ↔
      ¬∃ σ : BehavioralPolicy sys,
        actualTerminalScore sys σ (rationalInitialRow μ hμ hμ1) N
          (fun y => (danger y : ℝ)) ≤ (ρ : ℝ) := by
  rw [solveRiskFlow_none_iff sys μ reward danger hμ hμ1 ρ]
  constructor
  · intro hn ⟨σ,hσ⟩
    apply hn
    refine ⟨occupancies sys σ (rationalInitialRow μ hμ hμ1) N, ?_⟩
    rwa [← actualTerminalScore_eq_flowValue]
  · intro hn ⟨F,hF⟩
    apply hn
    refine ⟨F.policy, ?_⟩
    rwa [actualTerminalScore_reconstructed]

/-- One actual controller realizes the exact returned rational flow and the
simultaneous risk/success optimum over all legal behavioral histories. -/
theorem solveRiskFlow_some_actual_optimal (sys : TimeSystem C n)
    (μ reward danger : Fin n → ℚ) (hμ : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (ρ : ℚ)
    (q : FlowCoordinate C n N → ℚ) (hq : solveRiskFlow sys μ reward danger ρ = some q) :
    ∃ σ : BehavioralPolicy sys,
      (occupancies sys σ (rationalInitialRow μ hμ hμ1) N).vector = (fun j => (q j : ℝ)) ∧
      actualTerminalScore sys σ (rationalInitialRow μ hμ hμ1) N
        (fun y => (danger y : ℝ)) ≤ (ρ : ℝ) ∧
      actualTerminalScore sys σ (rationalInitialRow μ hμ hμ1) N
        (fun y => (reward y : ℝ)) = (dotProduct (terminalExpression reward) q : ℚ) ∧
      ∀ τ : BehavioralPolicy sys,
        actualTerminalScore sys τ (rationalInitialRow μ hμ hμ1) N
          (fun y => (danger y : ℝ)) ≤ (ρ : ℝ) →
        actualTerminalScore sys τ (rationalInitialRow μ hμ hμ1) N
          (fun y => (reward y : ℝ)) ≤
        actualTerminalScore sys σ (rationalInitialRow μ hμ hμ1) N
          (fun y => (reward y : ℝ)) := by
  obtain ⟨F,hv,hr,hm⟩ := solveRiskFlow_some_optimal sys μ reward danger hμ hμ1 ρ q hq
  refine ⟨F.policy, F.vector_policy.trans hv, ?_, ?_, ?_⟩
  · rw [actualTerminalScore_reconstructed]
    exact hr
  · rw [actualTerminalScore_reconstructed, F.terminalValue_eq_evaluate, hv]
    simp [evaluate, dotProduct]
  · intro τ hτ
    rw [actualTerminalScore_eq_flowValue] at hτ ⊢
    rw [actualTerminalScore_reconstructed]
    exact hm (occupancies sys τ (rationalInitialRow μ hμ hμ1) N) hτ

end PermanssonResearch.ReverseSolver.Occupancy
