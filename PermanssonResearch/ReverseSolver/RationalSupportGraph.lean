import PermanssonResearch.ReverseSolver.CheckedRationalInput
import PermanssonResearch.ReverseSolver.RationalTypedSupportBridge
import Mathlib.Tactic

/-!
# C10 — executable strict-positive graph and Floyd–Warshall closure

Graph queries use exact rational `0 < entry`, never a floating threshold.
The zero-length reachability path is included in the seed relation.
The typed one-step and logical path transport are already proved in C9.
-/
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- A computable strict-positive edge relation. -/
def edgeB {n : ℕ} (K : RationalMarkovMatrix n)
    (x z : Fin n) : Bool := decide (0 < K.entry x z)

theorem edgeB_true_iff {n : ℕ} (K : RationalMarkovMatrix n)
    (x z : Fin n) : edgeB K x z = true ↔ 0 < K.entry x z := by
  simp [edgeB]

/-- The diagonal represents paths of length zero. -/
def reachSeed {n : ℕ} (K : RationalMarkovMatrix n)
    (x z : Fin n) : Bool := decide (x = z) || edgeB K x z


/-- Exact Boolean disjunction on the executable adjacency table. -/
theorem orB_eq_true_iff (p q : Bool) :
    (p || q) = true ↔ p = true ∨ q = true := by
  cases p <;> cases q <;> decide


/-- Constructive Boolean conjunction on exact finite tables. -/
theorem andB_eq_true_iff (p q : Bool) :
    (p && q) = true ↔ p = true ∧ q = true := by
  cases p <;> cases q <;> decide

def reachStep {n : ℕ} (R : Fin n → Fin n → Bool)
    (k : Fin n) (x z : Fin n) : Bool :=
  R x z || (R x k && R k z)

/-- Finite Floyd–Warshall closure; the order of intermediates is fixed
by the numeric state indices. -/
def reachTable {n : ℕ} (K : RationalMarkovMatrix n) :
    Fin n → Fin n → Bool :=
  (List.finRange n).foldl (fun R k => reachStep R k) (reachSeed K)

def reachesB {n : ℕ} (K : RationalMarkovMatrix n)
    (x z : Fin n) : Bool := reachTable K x z

/-- This decision is finite and independent of arbitrary Markov-kernel
class representatives; no noncomputable closure is evaluated at runtime. -/
def communicatesB {n : ℕ} (K : RationalMarkovMatrix n)
    (x z : Fin n) : Bool := reachesB K x z && reachesB K z x

/-- A positive matrix entry is always a seed graph edge. -/
theorem positive_seed {n : ℕ} (K : RationalMarkovMatrix n)
    (x z : Fin n) (hp : 0 < K.entry x z) :
    reachSeed K x z = true := by
  simp [reachSeed, edgeB, hp]

/-- Every starting state has its zero-length reachability seed. -/
theorem self_seed {n : ℕ} (K : RationalMarkovMatrix n)
    (x : Fin n) : reachSeed K x x = true := by
  simp [reachSeed]

end C10
end ReverseSolver
end PermanssonResearch