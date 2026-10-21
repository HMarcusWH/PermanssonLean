import PermanssonResearch.ReverseSolver.NonlinearPeriodThreeExpectedScore
import PermanssonResearch.MultipleLimit.FiniteKernelInvariantUniqueness
import Mathlib.Tactic

/-!
# N2: Complete physical-only deterministic feedback comparison

The original native strategic memory is Fin 3; the physical state/action
remain Bool and its P/U kernels are unchanged across policies. These lemmas
discharge the actual original-infinite-path objective for each physical-only
deterministic policy. The false-preserving case uses the *reached* bottom
class, not an arbitrary stationary mixture; the other cases use the exact
native invariant equations. This does not compare arbitrary randomized or
phase-aware stationary controllers.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace PermanssonResearch.ReverseSolver.NonlinearPeriodThree

open PermanssonLean
open PermanssonResearch.MultipleLimit.FiniteKernelInvariantUniqueness
open PermanssonResearch.MultipleLimit.FiniteKernelRealBridge
open PermanssonResearch.MultipleLimit.FiniteCesaroAlgebra
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
open PermanssonResearch.MultipleLimit.CanonicalClassSelector
open PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw
open PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
open PermanssonResearch.ReverseSolver.NonlinearOccupationBoundary

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov
set_option autoImplicit false

private noncomputable abbrev blindKernel (p : Bool → Bool) : Kernel State State :=
  (typedModel (phaseBlindPolicy p)).inducedKernel

private def falseState (i : Phase) : State := (i,false)
private def falseCycle : Set State := {y | y.2 = false}

/-- In the original six-state source, every phase-independent feedback
which keeps false at false rotates within the physical-false phase cycle. -/
private theorem false_next (p : Bool → Bool) (hf : p false = false)
    (i : Phase) :
    nextState (phaseBlindPolicy p) (falseState i) = falseState (i+1) := by
  simp [falseState, nextState, phaseBlindPolicy, hf]

private theorem false_cycle_edge (p : Bool → Bool) (hf : p false = false)
    (i : Phase) :
    PositiveEdge (blindKernel p) (falseState i) (falseState (i+1)) := by
  change 0 < (typedModel (phaseBlindPolicy p)).inducedKernel
    (falseState i) ({falseState (i+1)} : Set State)
  rw [induced_kernel_singleton, false_next p hf]
  simp

private theorem false_cycle_closed (p : Bool → Bool) (hf : p false = false) :
    ClosedSubset (blindKernel p) falseCycle := by
  intro y hy z hz
  change 0 < (typedModel (phaseBlindPolicy p)).inducedKernel
    y ({z} : Set State) at hz
  rw [induced_kernel_singleton] at hz
  have heq : nextState (phaseBlindPolicy p) y = z := by
    by_contra hn
    simp [hn] at hz
  subst z
  rcases y with ⟨i,b⟩
  have hb : b = false := by simpa [falseCycle] using hy
  subst b
  simp [falseCycle, false_next p hf, falseState]

private theorem false_cycle_comm (p : Bool → Bool) (hf : p false = false)
    (i : Phase) :
    Communicates (blindKernel p) (falseState 0) (falseState i) := by
  have h01 : Reachable (blindKernel p) (falseState 0) (falseState 1) := by
    simpa using reachable_single (blindKernel p) (false_cycle_edge p hf 0)
  have h12 : Reachable (blindKernel p) (falseState 1) (falseState 2) := by
    simpa using reachable_single (blindKernel p) (false_cycle_edge p hf 1)
  have h20 : Reachable (blindKernel p) (falseState 2) (falseState 0) := by
    simpa [show (2 : Phase) + 1 = 0 by decide] using
      reachable_single (blindKernel p) (false_cycle_edge p hf 2)
  fin_cases i
  · exact communicates_refl (blindKernel p) _
  · exact ⟨h01,reachable_trans (blindKernel p) h12 h20⟩
  · exact ⟨reachable_trans (blindKernel p) h01 h12,h20⟩

private theorem false_cycle_eq_class (p : Bool → Bool) (hf : p false = false) :
    falseCycle = CommunicatingClass (blindKernel p) (falseState 0) := by
  ext y
  constructor
  · intro hy
    rcases y with ⟨i,b⟩
    have hb : b = false := by simpa [falseCycle] using hy
    subst b
    exact false_cycle_comm p hf i
  · intro hy
    exact closed_reachable (blindKernel p) (false_cycle_closed p hf)
      (by simp [falseCycle, falseState]) hy.1

private theorem false_cycle_recurrent (p : Bool → Bool) (hf : p false = false) :
    falseCycle ∈ RecurrentClasses (blindKernel p) := by
  have hrec : IsRecurrentState (blindKernel p) (falseState 0) := by
    change ClosedSubset (blindKernel p)
      (CommunicatingClass (blindKernel p) (falseState 0))
    rw [← false_cycle_eq_class p hf]
    exact false_cycle_closed p hf
  exact (recurrentClasses_mem_iff (blindKernel p) _).mpr
    ⟨falseState 0, hrec,(false_cycle_eq_class p hf).symm⟩

private theorem blind_orbit_false (p : Bool → Bool) (hf : p false = false)
    (n : ℕ) :
    (nativeOrbit (phaseBlindPolicy p) n).2 = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change p (nativeOrbit (phaseBlindPolicy p) n).2 = false
      rw [ih]
      exact hf

/-- The chosen native Markov class remains the physical-false 3-cycle
for BOTH false-preserving stationary Bool-only feedback controllers. -/
private theorem false_cycle_selected (p : Bool → Bool) (hf : p false = false) :
    CommunicatingClass (blindKernel p)
      (selectedRepresentative (blindKernel p)
        (nativeOrbit (phaseBlindPolicy p))) = falseCycle := by
  let w : ℕ → State := nativeOrbit (phaseBlindPolicy p)
  have h0recurrent : falseState 0 ∈ RecurrentStates (blindKernel p) := by
    change ClosedSubset (blindKernel p)
      (CommunicatingClass (blindKernel p) (falseState 0))
    rw [← false_cycle_eq_class p hf]
    exact false_cycle_closed p hf
  have hHit : HasRecurrentHit (blindKernel p) w := by
    refine ⟨0,?_⟩
    change start ∈ RecurrentStates (blindKernel p)
    exact h0recurrent
  have hfirst : firstRecurrentState (blindKernel p) w ∈ falseCycle := by
    change (w (firstRecurrentIndex (blindKernel p) w)).2 = false
    exact blind_orbit_false p hf _
  have hfirstComm : Communicates (blindKernel p)
      (falseState 0) (firstRecurrentState (blindKernel p) w) := by
    rw [false_cycle_eq_class p hf] at hfirst
    exact hfirst
  have hfirstClass :
      CommunicatingClass (blindKernel p)
          (firstRecurrentState (blindKernel p) w) = falseCycle := by
    calc
      _ = CommunicatingClass (blindKernel p) (falseState 0) :=
        (communicatingClass_eq_of_communicates (blindKernel p) hfirstComm).symm
      _ = falseCycle := (false_cycle_eq_class p hf).symm
  have hrep : selectedRepresentative (blindKernel p) w ∈ falseCycle := by
    have hc : classRepresentative (blindKernel p)
          (firstRecurrentState (blindKernel p) w) ∈ falseCycle := by
      rw [← hfirstClass]
      exact classRepresentative_mem (blindKernel p) _
    simpa [selectedRepresentative, hHit] using hc
  have hCommRep : Communicates (blindKernel p) (falseState 0)
      (selectedRepresentative (blindKernel p) w) := by
    rw [false_cycle_eq_class p hf] at hrep
    exact hrep
  calc
    CommunicatingClass (blindKernel p)
        (selectedRepresentative (blindKernel p) w) =
        CommunicatingClass (blindKernel p) (falseState 0) :=
      (communicatingClass_eq_of_communicates (blindKernel p) hCommRep).symm
    _ = falseCycle := (false_cycle_eq_class p hf).symm

/-- Actual physical true-state mass is ZERO for the real original point
start when the deterministic policy does not leave physical false. -/
theorem native_false_preserving_true_mass_zero
    (p : Bool → Bool) (hf : p false = false) :
    (((physicalOccupationLimit (blindKernel p)
      (nativeOrbit (phaseBlindPolicy p))).map Prod.snd).toMeasure
      ({true} : Set Bool)).toReal = 0 := by
  have hclass :
      physicalOccupationLimit (blindKernel p)
          (nativeOrbit (phaseBlindPolicy p)) =
        stationaryForSet (blindKernel p) falseCycle := by
    unfold physicalOccupationLimit
    rw [false_cycle_selected p hf]
  rw [hclass]
  let π := stationaryForSet (blindKernel p) falseCycle
  have hsupp : π.toMeasure falseCycle = 1 :=
    (stationaryForSet_spec (blindKernel p) (false_cycle_recurrent p hf)).2
  have hpre :
      (Prod.snd ⁻¹' ({true} : Set Bool) : Set State) = falseCycleᶜ := by
    ext y
    cases y.2 <;> simp [falseCycle]
  have hmeas : MeasurableSet falseCycle :=
    (Set.toFinite falseCycle).measurableSet
  rw [ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (by fun_prop) (measurableSet_singleton true), hpre]
  rw [prob_compl_eq_one_sub hmeas, hsupp]
  norm_num

/-- An original stationary physical-true marginal equals the sum of the
three genuine native-state singleton masses. -/
private theorem physical_true_mass_eq_sum (π : ProbabilityMeasure State) :
    ((π.map Prod.snd).toMeasure ({true} : Set Bool)).toReal =
      ∑ i : Phase, realPointMass π (i,true) := by
  classical
  let s : Finset State := Finset.univ.filter (fun y => y.2 = true)
  have hs : (Prod.snd ⁻¹' ({true} : Set Bool) : Set State) =
      (↑s : Set State) := by
    ext y
    simp [s]
  rw [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton true), hs]
  rw [sum_measure_singleton]
  rw [ENNReal.toReal_sum (fun i hi => measure_ne_top π.toMeasure _)]
  change (∑ y ∈ s, realPointMass π y) = ∑ i : Phase, realPointMass π (i,true)
  simp [s,Fintype.sum_prod_type,Fintype.sum_bool]

private theorem blind_real_transition (p : Bool → Bool) (y z : State) :
    realTransition (blindKernel p) y z =
      if nextState (phaseBlindPolicy p) y = z then (1 : ℝ) else 0 := by
  change (((typedModel (phaseBlindPolicy p)).inducedKernel y
    ({z} : Set State)).toReal) = _
  rw [induced_kernel_singleton]
  split_ifs <;> simp

/-- The two policies with p(false)=true have either a constant true world
(p(true)=true) or an alternating Bool world (p(true)=false). Any native
invariant law consequently has projected physical true mass 1 or 1/2.
This uses the ORIGINAL six-state stochastic rows and stationary equations. -/
private theorem blind_invariant_true_mass
    (p : Bool → Bool) (hf : p false = true)
    (π : ProbabilityMeasure State)
    (hInv : Kernel.Invariant (blindKernel p) π.toMeasure) :
    ((π.map Prod.snd).toMeasure ({true} : Set Bool)).toReal =
      if p true then (1 : ℝ) else (1/2 : ℝ) := by
  classical
  let v : State → ℝ := realPointMass π
  have hsum : (∑ y : State, v y) = 1 := realPointMass_total π
  have hs (z : State) :
      (∑ y : State, v y *
        (if nextState (phaseBlindPolicy p) y = z then (1:ℝ) else 0)) = v z := by
    have h := realPointMass_stationary (blindKernel p) π hInv z
    change (∑ y : State,
      v y * realTransition (blindKernel p) y z) = v z at h
    simpa only [blind_real_transition] using h
  have h0 := hs (0,false)
  have h1 := hs (1,false)
  have h2 := hs (2,false)
  have h3 := hs (0,true)
  have h4 := hs (1,true)
  have h5 := hs (2,true)
  rw [physical_true_mass_eq_sum]
  change (∑ i : Phase, v (i,true)) = _
  simp only [Fin.sum_univ_three]
  simp only [Fintype.sum_prod_type,Fin.sum_univ_three,
    Fintype.sum_bool] at hsum
  cases ht : p true
  · simp [Fintype.sum_prod_type,Fin.sum_univ_three,Fintype.sum_bool,
      nextState,phaseBlindPolicy,nextPhase,hf,ht] at h0 h1 h2 h3 h4 h5
    simp only [ht, Bool.false_eq_true, ite_false]
    linarith [hsum,h0,h1,h2,h3,h4,h5]
  · simp [Fintype.sum_prod_type,Fin.sum_univ_three,Fintype.sum_bool,
      nextState,phaseBlindPolicy,nextPhase,hf,ht] at h0 h1 h2 h3 h4 h5
    simp only [ht, Bool.true_eq_true, ite_true]
    linarith [hsum,h0,h1,h2,h3,h4,h5]

/-- Actual original canonical expected nonlinear score for the
false-preserving physical-only policy class. -/
theorem native_false_preserving_score
    (p : Bool → Bool) (hf : p false = false) :
    nativeExpectedNonlinearScore (phaseBlindPolicy p) = (1/3 : ℝ) := by
  rw [native_expected_score_eq_actual_orbit]
  unfold nativeNonlinearPathScore booleanProbabilityScore
  rw [native_false_preserving_true_mass_zero p hf]
  norm_num

/-- Actual original canonical expected score for the other two Bool-only
feedback policies: constant true gives 2/3, alternation gives 5/6. -/
theorem native_true_after_false_score
    (p : Bool → Bool) (hf : p false = true) :
    nativeExpectedNonlinearScore (phaseBlindPolicy p) =
      if p true then (2/3 : ℝ) else (5/6 : ℝ) := by
  rw [native_expected_score_eq_actual_orbit]
  unfold nativeNonlinearPathScore booleanProbabilityScore
  have hInv : Kernel.Invariant (blindKernel p)
      (physicalOccupationLimit (blindKernel p)
        (nativeOrbit (phaseBlindPolicy p))).toMeasure :=
    (selectedStationary_spec (blindKernel p)
      (nativeOrbit (phaseBlindPolicy p))).1
  have hmass := blind_invariant_true_mass p hf
    (physicalOccupationLimit (blindKernel p)
      (nativeOrbit (phaseBlindPolicy p))) hInv
  rw [hmass]
  cases ht : p true <;> norm_num [ht]

/-- All four deterministic phase-blind stationary physical-feedback
policies have genuine expected nonlinear scores at most 5/6. -/
theorem native_phase_blind_actual_le_five_sixths
    (p : Bool → Bool) :
    nativeExpectedNonlinearScore (phaseBlindPolicy p) ≤ (5/6 : ℝ) := by
  cases h0 : p false
  · rw [native_false_preserving_score p h0]
    norm_num
  · rw [native_true_after_false_score p h0]
    cases h1 : p true <;> norm_num [h1]

/-- Alternating physical-only deterministic stationary feedback actually
attains the restricted optimum 5/6 in the original canonical model. -/
theorem native_phase_blind_actual_attained :
    nativeExpectedNonlinearScore
      (phaseBlindPolicy alternatingFeedback) = (5/6 : ℝ) := by
  rw [native_true_after_false_score alternatingFeedback (by decide)]
  norm_num [alternatingFeedback]

/-- The phase-aware ORIGINAL native-policy objective equals one and
strictly beats the original expected nonlinear objective of every
deterministic Bool-only stationary feedback on exactly the same P/U. -/
theorem native_actual_phase_aware_strictly_beats_phase_blind
    (p : Bool → Bool) :
    nativeExpectedNonlinearScore (phaseBlindPolicy p) <
      nativeExpectedNonlinearScore phaseAwarePolicy := by
  rw [native_phase_aware_actual_score_one]
  exact lt_of_le_of_lt (native_phase_blind_actual_le_five_sixths p)
    (by norm_num)

end PermanssonResearch.ReverseSolver.NonlinearPeriodThree
