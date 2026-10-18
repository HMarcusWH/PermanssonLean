import PermanssonResearch.ReverseSolver.PolytopeOptimizer
import Mathlib.Topology.Order.Compact

/-! A list interface keeps the executable constraint enumeration explicit. -/

namespace PermanssonResearch.ReverseSolver.ExactPolytope

open Matrix Set

variable {J : Type*} [Fintype J] [DecidableEq J]

structure RationalConstraint (J : Type*) where
  coefficient : J → ℚ
  bound : ℚ

def RationalConstraint.holds (a : RationalConstraint J) (x : J → ℝ) : Prop :=
  (∑ j, (a.coefficient j : ℝ) * x j) ≤ (a.bound : ℝ)

def listFeasible (constraints : List (RationalConstraint J)) : Set (J → ℝ) :=
  {x | ∀ a ∈ constraints, a.holds x}

def listMatrix (constraints : List (RationalConstraint J)) :
    Matrix (Fin constraints.length) J ℚ := fun i => (constraints.get i).coefficient

def listBounds (constraints : List (RationalConstraint J)) : Fin constraints.length → ℚ :=
  fun i => (constraints.get i).bound

theorem listFeasible_eq (constraints : List (RationalConstraint J)) :
    listFeasible constraints = feasible (fun i j => (listMatrix constraints i j : ℝ))
      (fun i => (listBounds constraints i : ℝ)) := by
  ext x
  constructor
  · intro hx i
    exact hx (constraints.get i) (List.get_mem _ _)
  · intro hx a ha
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
    subst a
    simpa only [RationalConstraint.holds, dotProduct, listMatrix, listBounds] using hx i

theorem listFeasible_isCompact (constraints : List (RationalConstraint J))
    (lo hi : J → ℝ)
    (hb : ∀ x ∈ listFeasible constraints, lo ≤ x ∧ x ≤ hi) :
    IsCompact (listFeasible constraints) := by
  apply (isCompact_Icc (a := lo) (b := hi)).of_isClosed_subset
  · rw [listFeasible_eq]
    exact feasible_isClosed _ _
  · exact hb

def optimizeList (constraints : List (RationalConstraint J)) (c : J → ℚ) : Option (J → ℚ) :=
  optimizeRational (listMatrix constraints) (listBounds constraints) c

theorem optimizeList_none_iff (constraints : List (RationalConstraint J)) (c : J → ℚ)
    (lo hi : J → ℝ)
    (hb : ∀ x ∈ listFeasible constraints, lo ≤ x ∧ x ≤ hi) :
    optimizeList constraints c = none ↔ listFeasible constraints = ∅ := by
  rw [optimizeList, optimizeRational_none_iff _ _ _ (by
    rw [← listFeasible_eq]
    exact listFeasible_isCompact constraints lo hi hb), ← listFeasible_eq]

theorem optimizeList_some_feasible (constraints : List (RationalConstraint J))
    (c q : J → ℚ) (hq : optimizeList constraints c = some q) :
    (fun j => (q j : ℝ)) ∈ listFeasible constraints := by
  rw [listFeasible_eq]
  exact (rationalFeasible_iff_cast _ _ q).mp (optimizeRational_some_feasible _ _ c q hq)

theorem optimizeList_some_optimal (constraints : List (RationalConstraint J))
    (c q : J → ℚ) (hq : optimizeList constraints c = some q)
    (lo hi : J → ℝ)
    (hb : ∀ x ∈ listFeasible constraints, lo ≤ x ∧ x ≤ hi) :
    ∀ x ∈ listFeasible constraints,
      (∑ j : J, (c j : ℝ) * x j) ≤ (dotProduct c q : ℚ) := by
  rw [listFeasible_eq] at hb ⊢
  exact optimizeRational_some_optimal _ _ c q hq
    (by rw [← listFeasible_eq]; exact listFeasible_isCompact constraints lo hi (by
      rw [listFeasible_eq]; exact hb))

end PermanssonResearch.ReverseSolver.ExactPolytope
