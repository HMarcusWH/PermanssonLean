import PermanssonResearch.ReverseSolver.NonstationaryOptimality
import PermanssonResearch.ReverseSolver.BellmanExamples
import Mathlib.Tactic

/-!
# D1-C1: deadline-dependent probability and stationary reduction tests

The initial deadline is part of the process specification. Starting with
one transition remaining need not have the same first marginal as starting
with two transitions remaining, even for the same initial world state.
The stationary-policy special case does reduce to D1-A's canonical
finite-prefix law.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace NonstationaryExamples

open Nonstationary
open Bellman
open BellmanExamples
open ControlledKernel
open PermanssonLean.ProbabilitySupport

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- Genuine one-transition endpoint marginal of the nonstationary
Mathlib partialTraj law: the selected kernel at time zero. -/
theorem prefix_one_endpoint {C : Type*} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T : ℕ) (x : Fin n) :
    (prefixLaw sys π T x 1).map
      (fun w => w ⟨1, Finset.mem_Iic.mpr le_rfl⟩) =
    selectedKernel sys π T 0 x := by
  let κ : (k : ℕ) → Kernel ((i : Finset.Iic k) → Fin n) (Fin n) :=
    fun k => historyStep sys π T k
  have h := Kernel.map_partialTraj_succ_self
    (X := fun _ : ℕ => Fin n) (κ := κ) 0
  have hx := congrArg
    (fun Q : Kernel ((i : Finset.Iic 0) → Fin n) (Fin n) =>
      Q (singletonPrefix x)) h
  rw [Kernel.map_apply _ (by fun_prop)] at hx
  simpa [prefixLaw, historyStep, selectedKernel,
    singletonPrefix, κ] using hx

/-- Every one-step endpoint atom is the correct selected rational row. -/
theorem prefix_one_singleton {C : Type*} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (π : MarkovSchedule sys)
    (T : ℕ) (x z : Fin n) :
    prefixLaw sys π T x 1
      {w | w ⟨1, Finset.mem_Iic.mpr le_rfl⟩ = z} =
    ENNReal.ofReal ((selectedMatrix sys π T 0).entry x z : ℝ) := by
  have h := congrArg (fun μ : Measure (Fin n) => μ {z})
    (prefix_one_endpoint sys π T x)
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton z)] at h
  exact h.trans (rationalFiniteKernel_singleton (selectedMatrix sys π T 0) x z)

/-- When every elapsed-time rule is the SAME state-feedback function, the
true nonstationary law definition reduces definitionally to the D1-A
canonical stationary finite-prefix law. -/
theorem stationary_prefixLaw_eq {C : Type*} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (ρ : StateFeedback sys)
    (T t : ℕ) (x : Fin n) :
    prefixLaw sys (stationarySchedule ρ) T x t =
      finitePrefixLaw (rationalFiniteKernel (feedbackMatrix sys ρ)) x t := by
  rfl

/-- Exact D1-B deadline-dependent success probability under the ACTUAL
canonical rational time-inhomogeneous trajectory measure. -/
theorem deadline_success_exact :
    successProbability deadlineSystem deadlineSchedule deadlineTarget
      2 (0 : Fin 3) = ENNReal.ofReal (5/8 : ℝ) := by
  rw [successProbability_eq_policyValue, deadline_policy_five_eighths]
  norm_num

/-- A one-transition deadline chooses Gamble, so the first transition
hits goal with probability 1/2. -/
theorem deadline_one_first_goal :
    prefixLaw deadlineSystem deadlineSchedule 1 (0 : Fin 3) 1
      {w | w ⟨1, Finset.mem_Iic.mpr le_rfl⟩ = 1} =
      ENNReal.ofReal (1/2 : ℝ) := by
  rw [prefix_one_singleton]
  norm_num [selectedMatrix, deadlineSystem, deadlineSchedule,
    gambleMatrix, probeMatrix, feedbackMatrix]

/-- A two-transition deadline chooses Probe first, hitting goal in the
first transition with probability 1/4. -/
theorem deadline_two_first_goal :
    prefixLaw deadlineSystem deadlineSchedule 2 (0 : Fin 3) 1
      {w | w ⟨1, Finset.mem_Iic.mpr le_rfl⟩ = 1} =
      ENNReal.ofReal (1/4 : ℝ) := by
  rw [prefix_one_singleton]
  norm_num [selectedMatrix, deadlineSystem, deadlineSchedule,
    gambleMatrix, probeMatrix, feedbackMatrix]

/-- Genuine failure of cross-INITIAL-deadline projectivity. Even after
restricting both to the first transition the distributions are different. -/
theorem deadline_one_two_prefix_ne :
    prefixLaw deadlineSystem deadlineSchedule 2 (0 : Fin 3) 1 ≠
      prefixLaw deadlineSystem deadlineSchedule 1 (0 : Fin 3) 1 := by
  intro h
  have hpoint := congrArg (fun μ : Measure ((i : Finset.Iic 1) → Fin 3) =>
    μ {w | w ⟨1, Finset.mem_Iic.mpr le_rfl⟩ = 1}) h
  rw [deadline_two_first_goal, deadline_one_first_goal] at hpoint
  norm_num at hpoint

/-- The full two-transition run is projective within its original deadline,
but its restricted first transition differs from the run initialized at T=1. -/
theorem false_cross_deadline_projectivity :
    (prefixLaw deadlineSystem deadlineSchedule 2 (0 : Fin 3) 2).map
        (Preorder.frestrictLe₂ (π := fun _ : ℕ => Fin 3)
          (show 1 ≤ 2 by omega)) ≠
      prefixLaw deadlineSystem deadlineSchedule 1 (0 : Fin 3) 1 := by
  rw [prefixLaw_projective]
  exact deadline_one_two_prefix_ne

end NonstationaryExamples
end ReverseSolver
end PermanssonResearch
