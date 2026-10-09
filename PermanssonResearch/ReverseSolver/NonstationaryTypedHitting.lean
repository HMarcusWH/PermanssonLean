import PermanssonResearch.ReverseSolver.NonstationaryTypedTransport
import PermanssonResearch.ReverseSolver.NonstationaryOptimality
import Mathlib.Tactic

/-!
# D1-C2: first-hit probability and attained Bellman bound in actual typed law

The event is the already-certified D0 literal first-target-before-forbidden
measurable prefix event. Its preimage under D0's exact prefix encoding is
the typed event; the full-measure transport from D1-C2 and rational
correspondence from D1-C1 yield the exact probability identity.

No arbitrary externally supplied alpha/P/U or history-dependent policies
are included in the optimization claim.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace NonstationaryTyped

open Bellman
open ControlledKernel
open FiniteStrategicPathBridge
open Nonstationary

universe uC

/-- Literal first-hit event probability for the actual typed alpha/P/U
time-inhomogeneous strategic-world trajectory, at original deadline D. -/
noncomputable def typedSuccessProbability
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) : ℝ≥0∞ :=
  typedPrefixLaw sys pi D x D
    (successPrefixEvent (typedTarget target) D)

/-- First-hit probabilities are exactly preserved by the full-measure
typed/rational transport, with no redefined or approximate target event. -/
theorem typed_successProbability_eq_rational
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    typedSuccessProbability sys pi target D x =
      Nonstationary.successProbability sys pi target D x := by
  unfold typedSuccessProbability Nonstationary.successProbability
  have hmap := typed_prefixLaw_map sys pi D x D
  have hpre := prefixEncode_success_preimage target D
  rw [← hmap]
  rw [Measure.map_apply (measurable_prefixEncode D)
    (measurableSet_successPrefixEvent (rationalTargetAsFrozen target) D)]
  rw [hpre]

/-- Every admissible Markov schedule has a genuine typed first-hit event
probability exactly equal to its D1-B exact rational recursive value. -/
theorem typed_successProbability_eq_policyValue
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    typedSuccessProbability sys pi target D x =
      ENNReal.ofReal ((policyValue sys target pi D x : ℚ) : ℝ) := by
  rw [typed_successProbability_eq_rational,
    Nonstationary.successProbability_eq_policyValue]

/-- The original Bellman bound holds for actual typed time-dependent
strategic-world trajectories, not merely rational synthetic recursion. -/
theorem typed_successProbability_le_bellman
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    typedSuccessProbability sys pi target D x ≤
      ENNReal.ofReal ((bellmanValue sys target D x : ℚ) : ℝ) := by
  rw [typed_successProbability_eq_rational]
  exact Nonstationary.successProbability_le_bellman sys pi target D x

/-- The constructed D1-B maximizing schedule ATTAINS the optimal first-hit
probability under the actual typed time-varying alpha/P/U law. -/
theorem typed_maximizingSchedule_attains
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) (D : ℕ) (x : Fin n) :
    typedSuccessProbability sys (maximizingSchedule sys target)
      target D x =
      ENNReal.ofReal ((bellmanValue sys target D x : ℚ) : ℝ) := by
  rw [typed_successProbability_eq_rational]
  exact Nonstationary.maximizingSchedule_actual_probability sys target D x

end NonstationaryTyped
end ReverseSolver
end PermanssonResearch
