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
  Relation.ReflTransGen (PositiveEdge K) i j

def Communicates (i j : Y) : Prop :=
  (Reachable K) i j ∧ (Reachable K) j i

def CommunicatingClass (i : Y) : Set Y :=
  {j | (Communicates K) i j}

def ClosedSubset (C : Set Y) : Prop :=
  ∀ i ∈ C, ∀ j, (PositiveEdge K) i j → j ∈ C

theorem reachable_refl (i : Y) : (Reachable K) i i :=
  Relation.ReflTransGen.refl

theorem reachable_single {i j : Y} (hij : (PositiveEdge K) i j) :
    (Reachable K) i j :=
  Relation.ReflTransGen.single hij

theorem reachable_trans {i j k : Y}
    (hij : (Reachable K) i j) (hjk : (Reachable K) j k) :
    (Reachable K) i k :=
  Relation.ReflTransGen.trans hij hjk

theorem communicates_refl (i : Y) : (Communicates K) i i :=
  ⟨reachable_refl K i, reachable_refl K i⟩

theorem communicates_symm {i j : Y} (hij : (Communicates K) i j) :
    (Communicates K) j i :=
  ⟨hij.2, hij.1⟩

theorem communicates_trans {i j k : Y}
    (hij : (Communicates K) i j) (hjk : (Communicates K) j k) :
    (Communicates K) i k :=
  ⟨reachable_trans K hij.1 hjk.1, reachable_trans K hjk.2 hij.2⟩

theorem communicates_equivalence : Equivalence (Communicates K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact communicates_refl K i
  · intro i j hij
    exact communicates_symm K hij
  · intro i j k hij hjk
    exact communicates_trans K hij hjk

theorem mem_communicatingClass (i : Y) :
    i ∈ (CommunicatingClass K) i :=
  communicates_refl K i

theorem communicatingClass_eq_of_communicates {i j : Y}
    (hij : (Communicates K) i j) :
    (CommunicatingClass K) i = (CommunicatingClass K) j := by
  ext z
  constructor
  · intro hiz
    exact communicates_trans K (communicates_symm K hij) hiz
  · intro hjz
    exact communicates_trans K hij hjz

theorem communicatingClass_eq_of_common
    {i j z : Y}
    (hi : z ∈ (CommunicatingClass K) i)
    (hj : z ∈ (CommunicatingClass K) j) :
    (CommunicatingClass K) i = (CommunicatingClass K) j := by
  exact (communicatingClass_eq_of_communicates K hi).trans
    (communicatingClass_eq_of_communicates K hj).symm

theorem communicatingClass_disjoint_or_eq (i j : Y) :
    Disjoint ((CommunicatingClass K) i) ((CommunicatingClass K) j) ∨
      (CommunicatingClass K) i = (CommunicatingClass K) j := by
  classical
  by_cases h : ∃ z, z ∈ (CommunicatingClass K) i ∧
      z ∈ (CommunicatingClass K) j
  · right
    rcases h with ⟨z, hi, hj⟩
    exact communicatingClass_eq_of_common K hi hj
  · left
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact h ⟨z, hi, hj⟩

theorem closed_reachable {C : Set Y} (hC : (ClosedSubset K) C)
    {i j : Y} (hi : i ∈ C) (hij : (Reachable K) i j) :
    j ∈ C := by
  induction hij with
  | refl => exact hi
  | tail hab hbc ih => exact hC _ ih _ hbc

theorem closed_union (C D : Set Y)
    (hC : (ClosedSubset K) C) (hD : (ClosedSubset K) D) :
    (ClosedSubset K) (C ∪ D) := by
  intro i hi j hij
  rcases hi with hiC | hiD
  · exact Or.inl (hC i hiC j hij)
  · exact Or.inr (hD i hiD j hij)

theorem closed_univ : (ClosedSubset K) Set.univ := by
  intro i hi j hij
  trivial

/-- Every finite transition graph has a reachable terminal communicating
class. The preorder maximality is for *positive-probability reachability*,
not for the ambient order of the finite type. -/
theorem exists_reachable_closed_class (y : Y) :
    ∃ c : Y, (Reachable K) y c ∧
      (ClosedSubset K) ((CommunicatingClass K) c) := by
  classical
  letI : Preorder Y := {
    le := (Reachable K)
    le_refl := reachable_refl K
    le_trans := fun _ _ _ hab hbc => reachable_trans K hab hbc
  }
  obtain ⟨c, hyc, hc⟩ :=
    Finite.exists_le_maximal (p := fun z : Y => (Reachable K) y z)
      (reachable_refl K y)
  have hterminal (z : Y) (hcz : (Reachable K) c z) :
      (Reachable K) z c := by
    exact hc.2 (reachable_trans K hyc hcz) hcz
  refine ⟨c, hyc, ?_⟩
  intro i hi j hij
  have hcj : (Reachable K) c j :=
    reachable_trans K hi.1 (reachable_single K hij)
  exact ⟨hcj, hterminal j hcj⟩

/-- The previous result gives a closed communicating class which is
reachable from each initial state, *without* selecting a distinguished
physical class ahead of time. -/
theorem exists_closed_reachable_set (y : Y) :
    ∃ C : Set Y, C.Nonempty ∧ (ClosedSubset K) C ∧
      ∃ c ∈ C, (Reachable K) y c := by
  obtain ⟨c, hyc, hclosed⟩ := exists_reachable_closed_class K y
  exact ⟨(CommunicatingClass K) c, ⟨c, mem_communicatingClass K c⟩,
    hclosed, c, mem_communicatingClass K c, hyc⟩

end KernelCommunication
end MultipleLimit
end PermanssonResearch
