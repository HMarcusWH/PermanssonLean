import PermanssonResearch.ReverseSolver.ChronologicalFiniteLaw
import Mathlib.Tactic

/-!
# M-02 — equal unmarked key law, incompatible action-marked joint laws

Two finite normalized probability laws over (key, realized action) agree
on EVERY key marginal. In the first law the action equals the key, in the
second it is the negation. Their marked diagonal event probabilities are 1
and 0. This is a concrete nonvacuous failure of inference from an
unmarked state/key process to the actual marked action-history law.

This instantiates the existing FiniteProbabilityLaw interface; it is not
a derived conditional-product TwoPlayerGenerator instance or a claim about
unrestricted causal exogeneity. That protocol binding remains pending.
-/

namespace PermanssonResearch.MultiAgent.MarkedCouplingCountermodel

open PermanssonResearch.ReverseSolver.FiniteMonitor

/-- Two normalized actual joint atoms: key/action perfectly aligned. -/
def aligned : FiniteProbabilityLaw (Bool × Bool) where
  support := Finset.univ
  atom p := if p.1 = p.2 then (1/2 : ℝ) else 0
  nonnegative := by intro p; split <;> norm_num
  supported := by intro p hp; simp at hp
  normalized := by
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- A second normalized joint law with exactly opposite action coupling. -/
def crossed : FiniteProbabilityLaw (Bool × Bool) where
  support := Finset.univ
  atom p := if p.1 ≠ p.2 then (1/2 : ℝ) else 0
  nonnegative := by intro p; split <;> norm_num
  supported := by intro p hp; simp at hp
  normalized := by
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- This is a genuine marginalization of each joint law over actions. -/
def keyMass (L : FiniteProbabilityLaw (Bool × Bool)) (key : Bool) : ℝ :=
  ∑ action : Bool, L.atom (key, action)

/-- Equality of all unmarked key marginals despite changed action coupling. -/
theorem unmarked_key_laws_identical (key : Bool) :
    keyMass aligned key = keyMass crossed key := by
  cases key <;>
    norm_num [keyMass, aligned, crossed, Fintype.sum_bool]

/-- The visible key law is fair for both normalized joint models. -/
theorem key_marginals_fair (key : Bool) :
    keyMass aligned key = 1/2 ∧ keyMass crossed key = 1/2 := by
  cases key <;>
    norm_num [keyMass, aligned, crossed, Fintype.sum_bool]

/-- The same event is tested on the ACTUAL pair (key, action). -/
def diagonalEventMass (L : FiniteProbabilityLaw (Bool × Bool)) : ℝ :=
  ∑ p ∈ L.support, if p.1 = p.2 then L.atom p else 0

theorem aligned_diagonal_event_one : diagonalEventMass aligned = 1 := by
  norm_num [diagonalEventMass, aligned, Fintype.sum_prod_type, Fintype.sum_bool]

theorem crossed_diagonal_event_zero : diagonalEventMass crossed = 0 := by
  norm_num [diagonalEventMass, crossed, Fintype.sum_prod_type, Fintype.sum_bool]

/-- A single measurable finite marked event witnesses maximal separation. -/
theorem marked_joint_event_gap_one :
    |diagonalEventMass aligned - diagonalEventMass crossed| = 1 := by
  rw [aligned_diagonal_event_one, crossed_diagonal_event_zero]
  norm_num

end PermanssonResearch.MultiAgent.MarkedCouplingCountermodel
