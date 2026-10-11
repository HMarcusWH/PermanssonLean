import PermanssonResearch.MultipleLimit.FiniteCommunication
import Mathlib.Probability.Kernel.Irreducible
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic

/-!
# Lane C2 — generic finite-kernel communication and closed reachable classes

This module is genuinely generic in a finite *measurable* state type and
an arbitrary probability kernel, including irrational transition masses.
It does not require a pre-enumerated class list, a rational matrix or
aperiodicity. Edges are strictly positive actual singleton-kernel masses.

The finite maximal-reachable-element argument produces a reachable
closed communicating class from every initial point. This is a
graph-theoretic structural result. Canonical a.s. entry, stationary
class laws and the ergodic occupation theorem are separate obligations.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace KernelCommunication

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable (K : Kernel Y Y)

def PositiveEdge (i j : Y) : Prop :=
  0 < K i ({j} : Set Y)

def Reachable (i j : Y) : Prop :=
  Relation.ReflTransGen K.PositiveEdge i j

def Communicates (i j : Y) : Prop :=
  K.Reachable i j ∧ K.Reachable j i

def CommunicatingClass (i : Y) : Set Y :=
  {j | K.Communicates i j}

def ClosedSubset (C : Set Y) : Prop :=
  ∀ i ∈ C, ∀ j, K.PositiveEdge i j → j ∈ C

theorem reachable_refl (i : Y) : K.Reachable i i :=
  Relation.ReflTransGen.refl

theorem reachable_single {i j : Y} (hij : K.PositiveEdge i j) :
    K.Reachable i j :=
  Relation.ReflTransGen.single hij

theorem reachable_trans {i j k : Y}
    (hij : K.Reachable i j) (hjk : K.Reachable j k) :
    K.Reachable i k :=
  Relation.ReflTransGen.trans hij hjk

theorem communicates_refl (i : Y) : K.Communicates i i :=
  ⟨K.reachable_refl i, K.reachable_refl i⟩

theorem communicates_symm {i j : Y} (hij : K.Communicates i j) :
    K.Communicates j i :=
  ⟨hij.2, hij.1⟩

theorem communicates_trans {i j k : Y}
    (hij : K.Communicates i j) (hjk : K.Communicates j k) :
    K.Communicates i k :=
  ⟨K.reachable_trans hij.1 hjk.1, K.reachable_trans hjk.2 hij.2⟩

theorem communicates_equivalence : Equivalence K.Communicates :=
  ⟨K.communicates_refl, (fun _ _ => K.communicates_symm),
    (fun _ _ _ => K.communicates_trans)⟩

theorem mem_communicatingClass (i : Y) :
    i ∈ K.CommunicatingClass i :=
  K.communicates_refl i

theorem communicatingClass_eq_of_communicates {i j : Y}
    (hij : K.Communicates i j) :
    K.CommunicatingClass i = K.CommunicatingClass j := by
  ext z
  constructor
  · intro hiz
    exact K.communicates_trans (K.communicates_symm hij) hiz
  · intro hjz
    exact K.communicates_trans hij hjz

theorem communicatingClass_eq_of_common
    {i j z : Y}
    (hi : z ∈ K.CommunicatingClass i)
    (hj : z ∈ K.CommunicatingClass j) :
    K.CommunicatingClass i = K.CommunicatingClass j := by
  exact (K.communicatingClass_eq_of_communicates hi).trans
    (K.communicatingClass_eq_of_communicates hj).symm

theorem communicatingClass_disjoint_or_eq (i j : Y) :
    Disjoint (K.CommunicatingClass i) (K.CommunicatingClass j) ∨
      K.CommunicatingClass i = K.CommunicatingClass j := by
  classical
  by_cases h : ∃ z, z ∈ K.CommunicatingClass i ∧
      z ∈ K.CommunicatingClass j
  · right
    rcases h with ⟨z, hi, hj⟩
    exact K.communicatingClass_eq_of_common hi hj
  · left
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact h ⟨z, hi, hj⟩

theorem closed_reachable {C : Set Y} (hC : K.ClosedSubset C)
    {i j : Y} (hi : i ∈ C) (hij : K.Reachable i j) :
    j ∈ C := by
  induction hij with
  | refl => exact hi
  | tail hab hbc ih => exact hC _ ih _ hbc

theorem closed_union (C D : Set Y)
    (hC : K.ClosedSubset C) (hD : K.ClosedSubset D) :
    K.ClosedSubset (C ∪ D) := by
  intro i hi j hij
  rcases hi with hiC | hiD
  · exact Or.inl (hC i hiC j hij)
  · exact Or.inr (hD i hiD j hij)

theorem closed_univ : K.ClosedSubset Set.univ := by
  intro i hi j hij
  trivial

/-- Every finite transition graph has a reachable terminal communicating
class. The preorder maximality is for *positive-probability reachability*,
not for the ambient order of the finite type. -/
theorem exists_reachable_closed_class (y : Y) :
    ∃ c : Y, K.Reachable y c ∧
      K.ClosedSubset (K.CommunicatingClass c) := by
  classical
  letI : Preorder Y := {
    le := K.Reachable
    le_refl := K.reachable_refl
    le_trans := fun _ _ _ hab hbc => K.reachable_trans hab hbc
  }
  obtain ⟨c, hyc, hc⟩ :=
    Finite.exists_le_maximal (p := fun z : Y => K.Reachable y z)
      (K.reachable_refl y)
  have hterminal (z : Y) (hcz : K.Reachable c z) :
      K.Reachable z c := by
    exact hc.2 (K.reachable_trans hyc hcz) hcz
  refine ⟨c, hyc, ?_⟩
  intro i hi j hij
  have hcj : K.Reachable c j :=
    K.reachable_trans hi.1 (K.reachable_single hij)
  exact ⟨hcj, hterminal j hcj⟩

/-- The previous result gives a closed communicating class which is
reachable from each initial state, *without* selecting a distinguished
physical class ahead of time. -/
theorem exists_closed_reachable_set (y : Y) :
    ∃ C : Set Y, C.Nonempty ∧ K.ClosedSubset C ∧
      ∃ c ∈ C, K.Reachable y c := by
  obtain ⟨c, hyc, hclosed⟩ := K.exists_reachable_closed_class y
  exact ⟨K.CommunicatingClass c, ⟨c, K.mem_communicatingClass c⟩,
    hclosed, c, K.mem_communicatingClass c, hyc⟩

end KernelCommunication
end MultipleLimit
end PermanssonResearch
