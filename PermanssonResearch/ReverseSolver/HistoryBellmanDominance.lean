import PermanssonResearch.ReverseSolver.HistoryEventValue
import PermanssonResearch.ReverseSolver.NonstationaryOptimality
import Mathlib.Tactic

/-!
# D1-D1: one-step Bellman dominance and embedded optimizing witness

The remaining proof obligation for universal history-policy optimality is
to connect the exact path-event sum with the conditional first-successor
recursion at every supplied history. The one-step inequality below does
NOT by itself claim full horizon history-dependent dominance.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependent

open Bellman
open ControlledKernel

universe uC

/-- Every admissibly selected HISTORY-dependent control satisfies the
exact D1-B Bellman one-step upper bound on an unresolved history. -/
theorem history_step_bellman_upper
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (target : RationalHittingTarget n) (D i r : ℕ)
    (h : History n i)
    (hg : last h ∉ target.goal) (hf : last h ∉ target.forbidden) :
    (∑ z : Fin n, selectedEntry sys σ D i h z *
      bellmanValue sys target r z) ≤
      bellmanValue sys target (r+1) (last h) := by
  simpa [selectedEntry, actionScore] using
    (bellmanValue_succ_maximizes sys target r (last h) hg hf
      (σ.choose D i h) (σ.permitted D i h))

/-- Every embedded Markov policy has EXACTLY its previous D1-C1 first-hit
event probability under the new genuine history-dependent prefix measure. -/
theorem successProbability_embedMarkov
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    successProbability sys (embedMarkov sys π) target D x =
      Nonstationary.successProbability sys π target D x := by
  unfold successProbability Nonstationary.successProbability
  rw [prefixLaw_embedMarkov]

/-- D1-B's already-certified maximizing policy attains Bellman under the
GENUINE rational history-dependent trajectory law by exact embedding.
Universal dominance over all history policies remains a separate goal. -/
theorem embedded_maximizingSchedule_attains
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    successProbability sys
      (embedMarkov sys (maximizingSchedule sys target)) target D x =
        ENNReal.ofReal ((bellmanValue sys target D x : ℚ) : ℝ) := by
  rw [successProbability_embedMarkov]
  exact Nonstationary.maximizingSchedule_actual_probability sys target D x

end HistoryDependent
end ReverseSolver
end PermanssonResearch
