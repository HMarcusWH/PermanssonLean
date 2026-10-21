import PermanssonResearch.ReverseSolver.NonlinearPeriodThreeStationary
import PermanssonResearch.MultipleLimit.KernelCommunication
import PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
import PermanssonResearch.MultipleLimit.CanonicalClassSelector
import PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw
import PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
import Mathlib.Tactic

/-!
# Native S=Fin 3, X=Bool recurrent class and actual occupation identification

All states here are the true (phase, world) joint states of the original
alpha->P->U strategic model. The finite six-atom kernel is derived from P
and U, not a substituted Unit x Fin6 physical world.

This proves the reached native three-cycle is a closed communicating
class and the real canonical orbit selects precisely that class.
Stationary weight arithmetic remains an independent theorem obligation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace PermanssonResearch.ReverseSolver.NonlinearPeriodThree

open PermanssonLean
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
open PermanssonResearch.MultipleLimit.CanonicalClassSelector
open PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw
open PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov
set_option autoImplicit false

private noncomputable abbrev nativeK : Kernel State State :=
  (typedModel phaseAwarePolicy).inducedKernel

/-- Exactly the three reached native physical + strategic memory states. -/
def reachedCycle : Set State :=
  {canonicalCycleState (0 : Phase),
   canonicalCycleState (1 : Phase),
   canonicalCycleState (2 : Phase)}

theorem reachedCycle_mem (i : Phase) : canonicalCycleState i ∈ reachedCycle := by
  fin_cases i <;> simp [reachedCycle]

/-- Positive edge is proved from the real alpha-P-U induced kernel,
not a separately asserted graph. -/
theorem native_cycle_positive_edge (i : Phase) :
    PositiveEdge nativeK (canonicalCycleState i) (canonicalCycleState (i+1)) := by
  change 0 < (typedModel phaseAwarePolicy).inducedKernel
    (canonicalCycleState i) ({canonicalCycleState (i+1)} : Set State)
  rw [induced_kernel_singleton, native_cycle_successor]
  simp

private theorem reach01 :
    Reachable nativeK (canonicalCycleState 0) (canonicalCycleState 1) := by
  simpa using (reachable_single nativeK (native_cycle_positive_edge (0 : Phase)))

private theorem reach12 :
    Reachable nativeK (canonicalCycleState 1) (canonicalCycleState 2) := by
  simpa using (reachable_single nativeK (native_cycle_positive_edge (1 : Phase)))

private theorem reach20 :
    Reachable nativeK (canonicalCycleState 2) (canonicalCycleState 0) := by
  simpa [show (2 : Phase) + 1 = 0 by decide] using
    (reachable_single nativeK (native_cycle_positive_edge (2 : Phase)))

/-- All original native transitions from the selected three-cycle remain
inside the same three-cycle, including the wraparound. -/
theorem reachedCycle_closed : ClosedSubset nativeK reachedCycle := by
  intro y hy z hz
  change 0 < (typedModel phaseAwarePolicy).inducedKernel y ({z} : Set State) at hz
  rw [induced_kernel_singleton] at hz
  have hnext : nextState phaseAwarePolicy y = z := by
    by_contra hne
    simp [hne] at hz
  subst z
  have hcases : y = canonicalCycleState 0 ∨
        y = canonicalCycleState 1 ∨ y = canonicalCycleState 2 := by
    simpa [reachedCycle] using hy
  rcases hcases with h0 | h1 | h2
  · rw [h0, native_cycle_successor]
    exact reachedCycle_mem _
  · rw [h1, native_cycle_successor]
    exact reachedCycle_mem _
  · rw [h2, native_cycle_successor]
    exact reachedCycle_mem _

/-- Strong communication proved by three actual native positive edges. -/
theorem native_cycle_two_way_one :
    Communicates nativeK (canonicalCycleState 0) (canonicalCycleState 1) :=
  ⟨reach01, reachable_trans nativeK reach12 reach20⟩

theorem native_cycle_two_way_two :
    Communicates nativeK (canonicalCycleState 0) (canonicalCycleState 2) :=
  ⟨reachable_trans nativeK reach01 reach12, reach20⟩

/-- Native reached class coincides with the genuine Markov communicating
class, not just with the first three simulated orbit values. -/
theorem reachedCycle_eq_communicatingClass :
    reachedCycle = CommunicatingClass nativeK (canonicalCycleState 0) := by
  ext y
  constructor
  · intro hy
    have hcases : y = canonicalCycleState 0 ∨
          y = canonicalCycleState 1 ∨ y = canonicalCycleState 2 := by
      simpa [reachedCycle] using hy
    rcases hcases with h0 | h1 | h2
    · subst y
      exact communicates_refl nativeK _
    · subst y
      exact native_cycle_two_way_one
    · subst y
      exact native_cycle_two_way_two
  · intro hy
    exact closed_reachable nativeK reachedCycle_closed (reachedCycle_mem 0) hy.1

/-- The class is recurrent by the frozen communicating-class definition:
it is closed and strongly connected, without an aperiodicity assumption. -/
theorem reachedCycle_recurrent : reachedCycle ∈ RecurrentClasses nativeK := by
  have hrec : IsRecurrentState nativeK (canonicalCycleState 0) := by
    change ClosedSubset nativeK (CommunicatingClass nativeK (canonicalCycleState 0))
    rw [← reachedCycle_eq_communicatingClass]
    exact reachedCycle_closed
  exact (recurrentClasses_mem_iff nativeK _).mpr
    ⟨canonicalCycleState 0, hrec, reachedCycle_eq_communicatingClass.symm⟩

theorem native_phase_orbit_in_reachedCycle (n : ℕ) :
    nativeOrbit phaseAwarePolicy n ∈ reachedCycle := by
  rw [native_phase_orbit_is_cycle]
  exact reachedCycle_mem _

/-- The actual infinite canonical orbit reaches this recurrent class at time
zero and its genuine selectedRepresentative cannot select any other class. -/
theorem native_selected_communicatingClass :
    CommunicatingClass nativeK
        (selectedRepresentative nativeK (nativeOrbit phaseAwarePolicy)) =
      reachedCycle := by
  let w : ℕ → State := nativeOrbit phaseAwarePolicy
  have h0recurrent : canonicalCycleState 0 ∈ RecurrentStates nativeK := by
    change ClosedSubset nativeK
      (CommunicatingClass nativeK (canonicalCycleState 0))
    rw [← reachedCycle_eq_communicatingClass]
    exact reachedCycle_closed
  have hHit : HasRecurrentHit nativeK w := by
    refine ⟨0, ?_⟩
    change nativeOrbit phaseAwarePolicy 0 ∈ RecurrentStates nativeK
    rw [native_cycle_state_zero]
    exact h0recurrent
  have hfirst : firstRecurrentState nativeK w ∈ reachedCycle := by
    change w (firstRecurrentIndex nativeK w) ∈ reachedCycle
    exact native_phase_orbit_in_reachedCycle _
  have hfirstComm : Communicates nativeK
      (canonicalCycleState 0) (firstRecurrentState nativeK w) := by
    rw [reachedCycle_eq_communicatingClass] at hfirst
    exact hfirst
  have hfirstClass :
      CommunicatingClass nativeK (firstRecurrentState nativeK w) =
      reachedCycle := by
    calc
      _ = CommunicatingClass nativeK (canonicalCycleState 0) :=
        (communicatingClass_eq_of_communicates nativeK hfirstComm).symm
      _ = reachedCycle := reachedCycle_eq_communicatingClass.symm
  have hrep : selectedRepresentative nativeK w ∈ reachedCycle := by
    have hc : classRepresentative nativeK (firstRecurrentState nativeK w) ∈
        reachedCycle := by
      rw [← hfirstClass]
      exact classRepresentative_mem nativeK _
    simpa [selectedRepresentative, hHit] using hc
  have hCommRep : Communicates nativeK
      (canonicalCycleState 0) (selectedRepresentative nativeK w) := by
    rw [reachedCycle_eq_communicatingClass] at hrep
    exact hrep
  calc
    CommunicatingClass nativeK (selectedRepresentative nativeK w) =
        CommunicatingClass nativeK (canonicalCycleState 0) :=
      (communicatingClass_eq_of_communicates nativeK hCommRep).symm
    _ = reachedCycle := reachedCycle_eq_communicatingClass.symm

/-- Exact class identity of the actual original infinite-path occupation
limit; only explicit stationary weights/Bool projection remain to compute. -/
theorem native_actual_occupation_equals_reached_stationary :
    physicalOccupationLimit nativeK (nativeOrbit phaseAwarePolicy) =
      stationaryForSet nativeK reachedCycle := by
  unfold physicalOccupationLimit
  rw [native_selected_communicatingClass]

end PermanssonResearch.ReverseSolver.NonlinearPeriodThree
