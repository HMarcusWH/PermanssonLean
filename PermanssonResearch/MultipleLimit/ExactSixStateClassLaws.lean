import PermanssonResearch.MultipleLimit.ExactSixStateClassSelectionWeights
import PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
import Mathlib.Tactic

/-!
# C53-16 — physical six-state recurrent class identification

Proves that the two graph-closed physical blocks are EXACTLY the two
recurrent communicating classes of the genuine typed alpha/P/U Markov
kernel. Therefore their invariant probabilities are certified by
the generic existence/uniqueness theorem, even though A has period 2.

This is the bridge from a true selected class to its true stationary
probability measure. It rules out substituting the global stationary
barycenter for either physical pathwise limit.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateClassLaws

open PermanssonLean
open ReverseSolver.FiniteStrategicRealization
open ExactSixState
open ExactSixStateTyped
open ExactSixStateRecurrentGeometry
open ExactSixStateClassSelectionWeights
open KernelCommunication
open RecurrentClassDecomposition
open CanonicalClassSelector
open FiniteClassInvariantMeasure
open ClassStationarySelectionLaw
open FiniteOccupationRandomLaw

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

abbrev SixY := JointState Unit (Fin 6)
private abbrev K := typedModel.inducedKernel

theorem A_two_way :
    Communicates K (decode (2 : Fin 6)) (decode (3 : Fin 6)) := by
  constructor
  · apply reachable_single
    unfold PositiveEdge
    rw [typed_six_state_atom]
    norm_num [transition]
  · apply reachable_single
    unfold PositiveEdge
    rw [typed_six_state_atom]
    norm_num [transition]

theorem B_two_way :
    Communicates K (decode (4 : Fin 6)) (decode (5 : Fin 6)) := by
  constructor
  · apply reachable_single
    unfold PositiveEdge
    rw [typed_six_state_atom]
    norm_num [transition]
  · apply reachable_single
    unfold PositiveEdge
    rw [typed_six_state_atom]
    norm_num [transition]

theorem classASet_eq_commClass :
    classASet = CommunicatingClass K (decode (2 : Fin 6)) := by
  ext y
  constructor
  · intro hy
    have h : encode y = (2 : Fin 6) ∨ encode y = (3 : Fin 6) := hy
    rcases h with h2 | h3
    · have hEq : y = decode (2 : Fin 6) := by
        calc
          y = decode (encode y) := (decode_encode y).symm
          _ = decode (2 : Fin 6) := congrArg decode h2
      rw [hEq]
      exact communicates_refl K _
    · have hEq : y = decode (3 : Fin 6) := by
        calc
          y = decode (encode y) := (decode_encode y).symm
          _ = decode (3 : Fin 6) := congrArg decode h3
      rw [hEq]
      exact A_two_way
  · intro h
    have h2 : decode (2 : Fin 6) ∈ classASet := by
      norm_num [classASet, classA, encode, decode]
    exact closed_reachable K classASet_closed h2 h.1

theorem classBSet_eq_commClass :
    classBSet = CommunicatingClass K (decode (4 : Fin 6)) := by
  ext y
  constructor
  · intro hy
    have h : encode y = (4 : Fin 6) ∨ encode y = (5 : Fin 6) := hy
    rcases h with h4 | h5
    · have hEq : y = decode (4 : Fin 6) := by
        calc
          y = decode (encode y) := (decode_encode y).symm
          _ = decode (4 : Fin 6) := congrArg decode h4
      rw [hEq]
      exact communicates_refl K _
    · have hEq : y = decode (5 : Fin 6) := by
        calc
          y = decode (encode y) := (decode_encode y).symm
          _ = decode (5 : Fin 6) := congrArg decode h5
      rw [hEq]
      exact B_two_way
  · intro h
    have h4 : decode (4 : Fin 6) ∈ classBSet := by
      norm_num [classBSet, classB, encode, decode]
    exact closed_reachable K classBSet_closed h4 h.1

theorem classASet_recurrent : classASet ∈ RecurrentClasses K := by
  have hrec : IsRecurrentState K (decode (2 : Fin 6)) := by
    change ClosedSubset K (CommunicatingClass K (decode (2 : Fin 6)))
    rw [← classASet_eq_commClass]
    exact classASet_closed
  exact (recurrentClasses_mem_iff K _).mpr
    ⟨decode (2 : Fin 6), hrec, classASet_eq_commClass.symm⟩

theorem classBSet_recurrent : classBSet ∈ RecurrentClasses K := by
  have hrec : IsRecurrentState K (decode (4 : Fin 6)) := by
    change ClosedSubset K (CommunicatingClass K (decode (4 : Fin 6)))
    rw [← classBSet_eq_commClass]
    exact classBSet_closed
  exact (recurrentClasses_mem_iff K _).mpr
    ⟨decode (4 : Fin 6), hrec, classBSet_eq_commClass.symm⟩

/-- The true period-two and aperiodic invariant class probabilities,
constructed by the generic theorem rather than supplied as axioms. -/
noncomputable def πA : ProbabilityMeasure SixY :=
  stationaryForSet K classASet

noncomputable def πB : ProbabilityMeasure SixY :=
  stationaryForSet K classBSet

theorem πA_spec : Kernel.Invariant K πA.toMeasure ∧
    πA.toMeasure classASet = 1 :=
  stationaryForSet_spec K classASet_recurrent

theorem πB_spec : Kernel.Invariant K πB.toMeasure ∧
    πB.toMeasure classBSet = 1 :=
  stationaryForSet_spec K classBSet_recurrent

theorem selectedClass_eq_A_of_mem
    (w : ℕ → SixY)
    (hA : selectedRepresentative K w ∈ classASet) :
    CommunicatingClass K (selectedRepresentative K w) = classASet := by
  have hcomm : Communicates K (decode (2 : Fin 6))
      (selectedRepresentative K w) := by
    rw [classASet_eq_commClass] at hA
    exact hA
  calc
    CommunicatingClass K (selectedRepresentative K w) =
      CommunicatingClass K (decode (2 : Fin 6)) :=
      (communicatingClass_eq_of_communicates K hcomm).symm
    _ = classASet := classASet_eq_commClass.symm

theorem selectedClass_eq_B_of_mem
    (w : ℕ → SixY)
    (hB : selectedRepresentative K w ∈ classBSet) :
    CommunicatingClass K (selectedRepresentative K w) = classBSet := by
  have hcomm : Communicates K (decode (4 : Fin 6))
      (selectedRepresentative K w) := by
    rw [classBSet_eq_commClass] at hB
    exact hB
  calc
    CommunicatingClass K (selectedRepresentative K w) =
      CommunicatingClass K (decode (4 : Fin 6)) :=
      (communicatingClass_eq_of_communicates K hcomm).symm
    _ = classBSet := classBSet_eq_commClass.symm

theorem actualPhysicalLimit_eq_piA_of_selected_A
    (w : ℕ → SixY)
    (hA : selectedRepresentative K w ∈ classASet) :
    physicalOccupationLimit K w = πA := by
  simp only [physicalOccupationLimit, πA,
    selectedClass_eq_A_of_mem w hA]

theorem actualPhysicalLimit_eq_piB_of_selected_B
    (w : ℕ → SixY)
    (hB : selectedRepresentative K w ∈ classBSet) :
    physicalOccupationLimit K w = πB := by
  simp only [physicalOccupationLimit, πB,
    selectedClass_eq_B_of_mem w hB]

theorem classASet_disjoint_classBSet :
    Disjoint classASet classBSet := by
  apply Set.disjoint_left.mpr
  intro y hyA hyB
  exact Set.disjoint_left.mp classA_disjoint_classB hyA hyB

theorem πA_ne_πB : πA ≠ πB := by
  have hAB : classASet ⊆ classBSetᶜ := by
    intro y hA hB
    exact Set.disjoint_left.mp classASet_disjoint_classBSet hA hB
  have hBcomp : πB.toMeasure classBSetᶜ = 0 := by
    rw [prob_compl_eq_one_sub
      ((Set.toFinite classBSet).measurableSet), πB_spec.2]
    simp
  have hB_A : πB.toMeasure classASet = 0 :=
    measure_mono_null hAB hBcomp
  intro h
  have hh := congrArg (fun π : ProbabilityMeasure SixY =>
    π.toMeasure classASet) h
  rw [πA_spec.2, hB_A] at hh
  exact one_ne_zero hh

end ExactSixStateClassLaws
end MultipleLimit
end PermanssonResearch
