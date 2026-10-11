import PermanssonResearch.MultipleLimit.KernelCommunication
import Mathlib.Tactic

/-!
# Lane C2 — canonical finite communicating-class decomposition

Every finite Markov transition graph has a finite family of pairwise
disjoint closed communicating classes. Here class representatives
are de-duplicated extensionally as sets, not identified by arbitrary
numeric labels.

This is a structural graph-theoretic result for an arbitrary finite
measurable Markov kernel. The distinction between reachability and
almost-sure entry is preserved: a positive-probability graph path alone
does NOT certify an almost-sure trajectory event.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace RecurrentClassDecomposition

open KernelCommunication

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable (K : Kernel Y Y)

def IsRecurrentState (i : Y) : Prop :=
  ClosedSubset K (CommunicatingClass K i)

def RecurrentStates : Set Y :=
  {i | IsRecurrentState K i}

/-- A canonical FINITE family of distinct recurrent communicating
classes, without dependence on how the states are enumerated. -/
noncomputable def RecurrentClasses : Finset (Set Y) := by
  classical
  exact (Finset.univ.filter (IsRecurrentState K)).image (CommunicatingClass K)

theorem recurrent_of_communicates {i j : Y}
    (hi : IsRecurrentState K i) (hij : Communicates K i j) :
    IsRecurrentState K j := by
  change ClosedSubset K (CommunicatingClass K j)
  rw [← communicatingClass_eq_of_communicates K hij]
  exact hi

theorem recurrentStates_closed :
    ClosedSubset K (RecurrentStates K) := by
  intro i hi j hij
  change IsRecurrentState K i at hi
  have hclass : Communicates K i j :=
    hi i (mem_communicatingClass K i) j hij
  exact recurrent_of_communicates K hi hclass

theorem recurrentClasses_mem_iff (C : Set Y) :
    C ∈ RecurrentClasses K ↔
      ∃ i : Y, IsRecurrentState K i ∧ CommunicatingClass K i = C := by
  classical
  simp [RecurrentClasses]

theorem recurrentClasses_nonempty [Nonempty Y] :
    (RecurrentClasses K).Nonempty := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  obtain ⟨c, hyc, hclosed⟩ := exists_reachable_closed_class K y
  refine ⟨CommunicatingClass K c, ?_⟩
  exact (recurrentClasses_mem_iff K _).mpr ⟨c, hclosed, rfl⟩

theorem recurrentClasses_closed {C : Set Y}
    (hC : C ∈ RecurrentClasses K) :
    ClosedSubset K C := by
  obtain ⟨i, hi, rfl⟩ := (recurrentClasses_mem_iff K C).mp hC
  exact hi

theorem recurrentClasses_nonempty_class {C : Set Y}
    (hC : C ∈ RecurrentClasses K) :
    C.Nonempty := by
  obtain ⟨i, hi, rfl⟩ := (recurrentClasses_mem_iff K C).mp hC
  exact ⟨i, mem_communicatingClass K i⟩

theorem recurrentClasses_disjoint_of_ne {C D : Set Y}
    (hC : C ∈ RecurrentClasses K) (hD : D ∈ RecurrentClasses K)
    (hCD : C ≠ D) :
    Disjoint C D := by
  obtain ⟨i, hi, rfl⟩ := (recurrentClasses_mem_iff K C).mp hC
  obtain ⟨j, hj, rfl⟩ := (recurrentClasses_mem_iff K D).mp hD
  rcases communicatingClass_disjoint_or_eq K i j with hdisj | heq
  · exact hdisj
  · exact (hCD heq).elim

/-- Every finite state can graph-reach an actual member of some
closed recurrent communicating class. This is not yet the a.s. claim. -/
theorem exists_reachable_recurrent_state (y : Y) :
    ∃ z ∈ RecurrentStates K, Reachable K y z := by
  obtain ⟨z, hyz, hclosed⟩ := exists_reachable_closed_class K y
  exact ⟨z, hclosed, hyz⟩

theorem exists_reachable_recurrent_class (y : Y) :
    ∃ C ∈ RecurrentClasses K, ∃ z ∈ C, Reachable K y z := by
  obtain ⟨z, hyz, hclosed⟩ := exists_reachable_closed_class K y
  refine ⟨CommunicatingClass K z, ?_, z, mem_communicatingClass K z, hyz⟩
  exact (recurrentClasses_mem_iff K _).mpr ⟨z, hclosed, rfl⟩

/-- Every recurrent state is covered by the canonical finite class
family, and every member of such a class is recurrent. -/
theorem recurrentStates_iff_mem_recurrentClass (y : Y) :
    y ∈ RecurrentStates K ↔
      ∃ C ∈ RecurrentClasses K, y ∈ C := by
  constructor
  · intro hy
    refine ⟨CommunicatingClass K y, ?_, mem_communicatingClass K y⟩
    exact (recurrentClasses_mem_iff K _).mpr ⟨y, hy, rfl⟩
  · rintro ⟨C, hC, hyC⟩
    obtain ⟨z, hz, rfl⟩ := (recurrentClasses_mem_iff K C).mp hC
    exact recurrent_of_communicates K hz hyC

end RecurrentClassDecomposition
end MultipleLimit
end PermanssonResearch
