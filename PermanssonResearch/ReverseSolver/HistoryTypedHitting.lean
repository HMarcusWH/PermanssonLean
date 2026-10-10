import PermanssonResearch.ReverseSolver.HistoryTypedTransport
import PermanssonResearch.ReverseSolver.HistoryForwardMeasure
import PermanssonResearch.ReverseSolver.HistoryBellmanDominance
import Mathlib.Tactic

/-!
# D1-D2: original first-hit event transported to genuine typed histories

The literal D0 event is evaluated under the actual history-conditioned
typed alpha/P/U partialTraj law. D1-D1 gives universal history-policy
dominance, and its maximizing Markov embedding attains the exact bound.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependentTyped

open HistoryDependent Bellman ControlledKernel FiniteStrategicPathBridge

universe uC

/-- Genuine typed first-hit event probability at original deadline D. -/
noncomputable def typedSuccessProbability
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) : ℝ≥0∞ :=
  typedPrefixLaw sys σ D x D
    (successPrefixEvent (typedTarget target) D)

/-- EXACT probability equality for all admissible deterministic
history-dependent policies under the actual canonical typed trajectory. -/
theorem typed_successProbability_eq_rational
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    typedSuccessProbability sys σ target D x =
      HistoryDependent.successProbability sys σ target D x := by
  unfold typedSuccessProbability HistoryDependent.successProbability
  have hmap := typed_prefixLaw_map sys σ D x D
  have hpre := prefixEncode_success_preimage target D
  rw [← hmap]
  rw [Measure.map_apply (measurable_prefixEncode D)
    (measurableSet_successPrefixEvent (rationalTargetAsFrozen target) D)]
  rw [hpre]

/-- The history-dependent Bellman bound is valid on the actual typed
alpha/P/U-induced first-hit law, not only its rational representation. -/
theorem typed_successProbability_le_bellman
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    typedSuccessProbability sys σ target D x ≤
      ENNReal.ofReal ((bellmanValue sys target D x : ℚ) : ℝ) := by
  rw [typed_successProbability_eq_rational]
  exact HistoryDependent.successProbability_le_bellman sys σ target D x

/-- The embedded maximizing Markov schedule attains the exact Bellman
value under the genuine typed history-controlled trajectory law. -/
theorem typed_maximizingSchedule_attains
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    typedSuccessProbability sys
      (embedMarkov sys (maximizingSchedule sys target)) target D x =
      ENNReal.ofReal ((bellmanValue sys target D x : ℚ) : ℝ) := by
  rw [typed_successProbability_eq_rational]
  exact embedded_maximizingSchedule_attains sys target D x

/-- Exact fully observed typed history-dependent optimality: ALL admissible
deterministic complete-history controllers satisfy the bound and one
admissible embedded Markov controller attains it. -/
theorem typed_history_bellman_optimal_and_attained
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    (∀ σ : HistoryPolicy sys,
      typedSuccessProbability sys σ target D x ≤
        ENNReal.ofReal ((bellmanValue sys target D x : ℚ) : ℝ)) ∧
    (∃ σ : HistoryPolicy sys,
      typedSuccessProbability sys σ target D x =
        ENNReal.ofReal ((bellmanValue sys target D x : ℚ) : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro σ
    exact typed_successProbability_le_bellman sys σ target D x
  · exact ⟨embedMarkov sys (maximizingSchedule sys target),
      typed_maximizingSchedule_attains sys target D x⟩

end HistoryDependentTyped
end ReverseSolver
end PermanssonResearch
