import PermanssonResearch.MultipleLimit.AbsorbingFamily
import Mathlib.Tactic

/-!
# Lane C2 — genuine finite rational transition and communication primitives

Research-only. This file provides a finite, row-stochastic rational transition
object, positive-edge reachability, communication equivalence, and closed
subsets. It does NOT assert the finite recurrent-class classification theorem,
almost-sure hitting, stationarity or ergodic convergence.

A graph edge is strictly positive transition mass, not mere syntactic reachability.
The rational representation is deliberately distinguished from the original
ENNReal Markov kernel until an exact conversion theorem is proved.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteCommunication

structure RationalTransition (Y : Type*) [Fintype Y] where
  entry : Y → Y → ℚ
  nonneg : ∀ i j, 0 ≤ entry i j
  row_sum : ∀ i, ∑ j, entry i j = 1

namespace RationalTransition

variable {Y : Type*} [Fintype Y]
variable (T : RationalTransition Y)

def PositiveEdge (i j : Y) : Prop := 0 < T.entry i j

def Reachable (i j : Y) : Prop :=
  Relation.ReflTransGen T.PositiveEdge i j

def Communicates (i j : Y) : Prop :=
  T.Reachable i j ∧ T.Reachable j i

def ClosedSubset (C : Set Y) : Prop :=
  ∀ i ∈ C, ∀ j, T.PositiveEdge i j → j ∈ C

theorem reachable_refl (i : Y) : T.Reachable i i :=
  Relation.ReflTransGen.refl

theorem reachable_step {i j : Y} (h : T.PositiveEdge i j) :
    T.Reachable i j :=
  Relation.ReflTransGen.single h

theorem reachable_trans {i j k : Y}
    (hij : T.Reachable i j) (hjk : T.Reachable j k) :
    T.Reachable i k :=
  Relation.ReflTransGen.trans hij hjk

theorem communicates_refl (i : Y) : T.Communicates i i :=
  ⟨T.reachable_refl i, T.reachable_refl i⟩

theorem communicates_symm {i j : Y} (h : T.Communicates i j) :
    T.Communicates j i :=
  ⟨h.2, h.1⟩

theorem communicates_trans {i j k : Y}
    (hij : T.Communicates i j) (hjk : T.Communicates j k) :
    T.Communicates i k :=
  ⟨T.reachable_trans hij.1 hjk.1, T.reachable_trans hjk.2 hij.2⟩

theorem closed_univ : T.ClosedSubset Set.univ := by
  intro i hi j hij
  trivial

theorem closed_edge
    {C : Set Y} (hC : T.ClosedSubset C)
    {i j : Y} (hi : i ∈ C) (hij : T.PositiveEdge i j) :
    j ∈ C :=
  hC i hi j hij

end RationalTransition
end FiniteCommunication
end MultipleLimit
end PermanssonResearch
