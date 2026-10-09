import PermanssonResearch.ReverseSolver.HistoryBellmanDominance
import PermanssonResearch.ReverseSolver.NonstationaryExamples
import Mathlib.Tactic

/-!
# D1-D1: exact regression of D1-B/C1 benchmark through history embedding

A genuinely history-sensitive reachable-prefix witness and the universal
history-policy Bellman inequality remain subsequent proof obligations.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependentExamples

open HistoryDependent
open Bellman
open BellmanExamples
open ControlledKernel

/-- The original deadline-two 5/8 strategy is a valid history controller,
with the genuine new partialTraj probability exactly equal to 5/8. -/
theorem embedded_deadline_five_eighths :
    successProbability BellmanExamples.deadlineSystem
      (embedMarkov BellmanExamples.deadlineSystem BellmanExamples.deadlineSchedule)
      BellmanExamples.deadlineTarget 2 (0 : Fin 3) =
        ENNReal.ofReal (5/8 : ℝ) := by
  rw [successProbability_embedMarkov]
  exact NonstationaryExamples.deadline_success_exact


/-! ## Genuine positive-mass history-sensitive controller

Unlike the prior three-state 5/8 deadline example, these five states
contain two reachable histories that meet again at the SAME unresolved
state at the SAME time, after different earlier observations. -/

/-- Controls 0=branch, 1=win, 2=lose. At the start, branch randomly
visits state 1 or 2, both of which deterministically return to state 0.
State 3 is goal, 4 is forbidden; they alternate afterwards to ensure
that the physical kernel is emphatically NOT absorbing. -/
def reconvergeMatrix (c : Fin 3) : RationalMarkovMatrix 5 where
  entry := fun y z =>
    if y = 0 then
      if c = 0 then
        if z = 1 ∨ z = 2 then 1/2 else 0
      else if c = 1 then
        if z = 3 then 1 else 0
      else if z = 4 then 1 else 0
    else if y = 1 ∨ y = 2 then
      if z = 0 then 1 else 0
    else if y = 3 then
      if z = 4 then 1 else 0
    else
      if z = 3 then 1 else 0
  entry_nonneg := by
    intro y z
    split_ifs <;> norm_num
  row_sum_one := by
    intro y
    fin_cases y <;> fin_cases c <;>
      norm_num [Fin.sum_univ_five]

def reconvergeSystem : FiniteControlSystem (Fin 3) 5 where
  states_nonempty := by decide
  baseline := reconvergeMatrix 0
  options := fun _ => Finset.univ
  options_nonempty := by
    intro y
    exact ⟨0, Finset.mem_univ _⟩
  matrix := reconvergeMatrix

def reconvergeTarget : RationalHittingTarget 5 where
  goal := {3}
  forbidden := {4}
  disjoint := by simp

/-- The controller remembers which branch preceded the return to 0. -/
def reconvergePolicy : HistoryPolicy reconvergeSystem where
  choose := fun _ i w =>
    if hi : i = 2 then
      if w ⟨1, Finset.mem_Iic.mpr (by omega)⟩ = (1 : Fin 5)
      then 1 else 2
    else 0
  permitted := by
    intro D i w
    simp [reconvergeSystem]

def leftReturn : History 5 2 :=
  fun j => if (j : ℕ) = 1 then 1 else 0

def rightReturn : History 5 2 :=
  fun j => if (j : ℕ) = 1 then 2 else 0

/-- Two distinct histories, at identical elapsed time 2 and current state
0, lead to two different admissible controls. This genuinely exceeds the
state/time-only Markov policy grammar. -/
theorem reconverge_history_sensitive :
    last leftReturn = (0 : Fin 5) ∧
    last rightReturn = (0 : Fin 5) ∧
    reconvergePolicy.choose 3 2 leftReturn = (1 : Fin 3) ∧
    reconvergePolicy.choose 3 2 rightReturn = (2 : Fin 3) := by
  norm_num [reconvergePolicy, leftReturn, rightReturn, last]

/-- Each reconverged observed prefix is not merely a syntactic possibility:
it has exactly 1/2 mass under the REAL history-dependent prefix law. -/
theorem reconverge_left_mass :
    prefixLaw reconvergeSystem reconvergePolicy 3
      (0 : Fin 5) 2 {leftReturn} = ENNReal.ofReal (1/2 : ℝ) := by
  rw [prefix_atom_product]
  norm_num [rationalPathWeight, selectedEntry, observedPrefix,
    reconvergeSystem, reconvergePolicy, leftReturn, reconvergeMatrix,
    Fin.prod_univ_two, last]

theorem reconverge_right_mass :
    prefixLaw reconvergeSystem reconvergePolicy 3
      (0 : Fin 5) 2 {rightReturn} = ENNReal.ofReal (1/2 : ℝ) := by
  rw [prefix_atom_product]
  norm_num [rationalPathWeight, selectedEntry, observedPrefix,
    reconvergeSystem, reconvergePolicy, rightReturn, reconvergeMatrix,
    Fin.prod_univ_two, last]

end HistoryDependentExamples
end ReverseSolver
end PermanssonResearch
