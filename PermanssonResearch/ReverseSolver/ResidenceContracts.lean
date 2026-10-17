import PermanssonResearch.ReverseSolver.ResidenceValue
import PermanssonResearch.ReverseSolver.HistoryTypedHitting
import PermanssonResearch.RegimeExit.Proposition42f
import Mathlib.Tactic

/-!
# D2: existing reach/avoid and eventual-switch contracts; robust-order adversaries

The finite reach/avoid theorem is reused unchanged from D1. Eventual switching
consumes C69/C70 retention and routing, rather than treating a hit as retention.
The robust example is one decision: nature picks one fixed unobserved model,
then the controller draws its private action randomization. Nature knows p,
but not the realized action. Model-first optimization reveals the model to the
controller. There is no model learning, rectangularity, or robust recursion.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.ReverseSolver.Residence

open ControlledKernel HistoryDependent Bellman
open PermanssonLean.ProbabilitySupport
set_option autoImplicit false
universe uC

/-- D2.1/2 reuse: the actual typed goal-by-deadline strictly-before-danger
event is already solved by D1 for the fixed fully observed policy class. -/
theorem reachBeforeForbidden_optimal_and_attained
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (target : RationalHittingTarget n)
    (D : ℕ) (x : Fin n) :
    (∀ σ : HistoryPolicy sys,
      HistoryDependentTyped.typedSuccessProbability sys σ target D x ≤
        ENNReal.ofReal ((bellmanValue sys target D x : ℚ) : ℝ)) ∧
    (∃ σ : HistoryPolicy sys,
      HistoryDependentTyped.typedSuccessProbability sys σ target D x =
        ENNReal.ofReal ((bellmanValue sys target D x : ℚ) : ℝ)) :=
  HistoryDependentTyped.typed_history_bellman_optimal_and_attained sys target D x

/-- The C70 switching event literally includes every future target-region
observation, not just arrival or finite residence. Its probability bound is
the unchanged `RegimeExit.switchRetainEvent_prob_ge`. -/
theorem eventual_switch_event_semantics
    {S X H T : Type*} [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace H] [MeasurableSpace T]
    (source : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (target : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) T)
    (w : ℕ → PermanssonLean.JointState S X) :
    w ∈ RegimeExit.switchRetainEvent source target ↔
      ∃ k : ℕ, w ∈ RegimeExit.firstExitAtDestination source k target.basin ∧
        ∀ t ≥ k+1, w t ∈ target.region := Iff.rfl

/-- Model m=true succeeds on action a=true, model false on action false.
p is the probability of action true, committed before observing the model. -/
def robustSuccess (model : Bool) (p : ℚ) : ℚ := if model then p else 1-p

def robustCommitted (p : ℚ) : ℚ := min p (1-p)

theorem robustCommitted_optimum :
    IsGreatest {v : ℚ | ∃ p : ℚ, 0 ≤ p ∧ p ≤ 1 ∧ v = robustCommitted p} (1/2) := by
  constructor
  · exact ⟨1/2, by norm_num [robustCommitted]⟩
  · rintro v ⟨p, _, _, rfl⟩
    by_cases hp : p ≤ 1/2
    · exact (min_le_left _ _).trans hp
    · exact (min_le_right _ _).trans (by linarith)

/-- With the model revealed first, each model permits success probability one. -/
theorem modelFirst_optimum (model : Bool) :
    IsGreatest {v : ℚ | ∃ p : ℚ, 0 ≤ p ∧ p ≤ 1 ∧ v = robustSuccess model p} 1 := by
  cases model with
  | false =>
      constructor
      · exact ⟨0, by norm_num [robustSuccess]⟩
      · rintro v ⟨p, hp, _, rfl⟩
        have h : 1-p ≤ (1 : ℚ) := by linarith
        simpa [robustSuccess] using h
  | true =>
      constructor
      · exact ⟨1, by norm_num [robustSuccess]⟩
      · rintro v ⟨p, _, hp, rfl⟩; simpa [robustSuccess] using hp

/-- Exact strict max-min/min-max separation under the timing contract above. -/
theorem robust_quantifier_order_separation :
    IsGreatest {v : ℚ | ∃ p : ℚ, 0 ≤ p ∧ p ≤ 1 ∧ v = robustCommitted p} (1/2) ∧
    (∀ model : Bool,
      IsGreatest {v : ℚ | ∃ p : ℚ, 0 ≤ p ∧ p ≤ 1 ∧ v = robustSuccess model p} 1) ∧
    (1/2 : ℚ) < 1 :=
  ⟨robustCommitted_optimum, modelFirst_optimum, by norm_num⟩

theorem deterministic_robust_zero :
    robustCommitted 0 = 0 ∧ robustCommitted 1 = 0 := by
  norm_num [robustCommitted]

/-- Mixture of safe (.8 success, no danger) and risky (.9 success, .1 danger).
p is the risky probability; both are one-step, mutually exclusive outcomes. -/
def riskSuccess (p : ℚ) : ℚ := 4/5 + p/10

def riskProbability (p : ℚ) : ℚ := p/10

theorem hard_risk_budget_optimum :
    IsGreatest {v : ℚ | ∃ p : ℚ, 0 ≤ p ∧ p ≤ 1 ∧
      riskProbability p ≤ 1/20 ∧ v = riskSuccess p} (17/20) := by
  constructor
  · exact ⟨1/2, by norm_num [riskProbability, riskSuccess]⟩
  · rintro v ⟨p, _, _, hrisk, rfl⟩
    unfold riskProbability at hrisk
    unfold riskSuccess
    linarith

/-- Unconstrained success maximization selects an infeasible risky action. -/
theorem unconstrained_success_is_not_risk_constrained :
    riskSuccess 0 < riskSuccess 1 ∧
    ¬ riskProbability 1 ≤ 1/20 ∧
    riskSuccess (1/2) = 17/20 := by
  norm_num [riskSuccess, riskProbability]

end PermanssonResearch.ReverseSolver.Residence
