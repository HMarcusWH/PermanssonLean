import PermanssonResearch.ReverseSolver.NonlinearPeriodThreePathLaw
import PermanssonLean.Regime.Occupation
import PermanssonResearch.MultipleLimit.FiniteKernelInvariantUniqueness
import Mathlib.Tactic

/-!
Native three-phase occupation witness. This certifies the real alpha-P-U
orbit and an explicit normalized candidate cycle law. Equality to the
canonical selected stationary law is NOT silently inferred.
-/
open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.ReverseSolver.NonlinearPeriodThree
open PermanssonLean
open PermanssonLean.RegimeSpecification

def canonicalCycleState (i : Phase) : State := (i, i != 0)

theorem native_cycle_state_zero : canonicalCycleState 0 = start := by decide
theorem native_cycle_state_one : canonicalCycleState 1 = (1,true) := by decide
theorem native_cycle_state_two : canonicalCycleState 2 = (2,true) := by decide

theorem native_cycle_successor (i : Phase) :
    nextState phaseAwarePolicy (canonicalCycleState i) =
      canonicalCycleState (i+1) := by
  fin_cases i <;> decide

def phaseIndex : ℕ → Phase
  | 0 => 0
  | n+1 => phaseIndex n + 1

theorem native_phase_orbit_is_cycle (n : ℕ) :
    nativeOrbit phaseAwarePolicy n = canonicalCycleState (phaseIndex n) := by
  induction n with
  | zero => exact native_cycle_state_zero.symm
  | succ n ih =>
      rw [nativeOrbit, phaseIndex, ih]
      exact native_cycle_successor (phaseIndex n)

noncomputable def exactCycleLaw : ProbabilityMeasure State :=
  (uniformFinProbability 3 (by norm_num)).map canonicalCycleState

theorem native_three_phase_true_share :
    ((if (canonicalCycleState 0).2 then (1:ℚ) else 0) +
      (if (canonicalCycleState 1).2 then (1:ℚ) else 0) +
      (if (canonicalCycleState 2).2 then (1:ℚ) else 0))/3 = 2/3 := by
  norm_num [canonicalCycleState]


/-!
## Exact invariant weights on the genuine native six-state Markov chain

This is the genuine original alpha-P-U kernel. Any invariant probability
must concentrate on the unique physically reached three-phase cycle;
its three nonzero stationary point masses are all one third. No C11
Unit/Fin6 strategic-world re-encoding or assumed numerical table appears.
-/

open PermanssonResearch.MultipleLimit.FiniteKernelInvariantUniqueness
open PermanssonResearch.MultipleLimit.FiniteKernelRealBridge
open PermanssonResearch.MultipleLimit.FiniteCesaroAlgebra
attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- Every real singleton transition probability is exactly the genuine
native alpha-P-U deterministic row, not an externally asserted matrix. -/
theorem phase_aware_real_transition (y z : State) :
    realTransition (typedModel phaseAwarePolicy).inducedKernel y z =
      if nextState phaseAwarePolicy y = z then (1 : ℝ) else 0 := by
  change (((typedModel phaseAwarePolicy).inducedKernel y
    ({z} : Set State)).toReal) = _
  rw [induced_kernel_singleton]
  split_ifs <;> simp

/-- Finite stationary equations for the real native model force *all six*
point masses. In particular the three off-cycle states have probability
zero; the period-three class has equal point weights 1/3. -/
theorem phase_aware_invariant_weights
    (π : ProbabilityMeasure State)
    (hInv : Kernel.Invariant
      (typedModel phaseAwarePolicy).inducedKernel π.toMeasure) :
    realPointMass π start = (1/3 : ℝ) ∧
    realPointMass π (1,true) = (1/3 : ℝ) ∧
    realPointMass π (2,true) = (1/3 : ℝ) ∧
    realPointMass π (0,true) = 0 ∧
    realPointMass π (1,false) = 0 ∧
    realPointMass π (2,false) = 0 := by
  classical
  let v : State → ℝ := realPointMass π
  have hsum : (∑ y : State, v y) = 1 :=
    realPointMass_total π
  have hstat (z : State) :
      (∑ y : State, v y *
        (if nextState phaseAwarePolicy y = z then (1:ℝ) else 0)) = v z := by
    have h := realPointMass_stationary
      (typedModel phaseAwarePolicy).inducedKernel π hInv z
    change (∑ y : State,
      v y * realTransition (typedModel phaseAwarePolicy).inducedKernel y z) = v z at h
    simpa only [phase_aware_real_transition] using h
  have h0 := hstat (0,false)
  have h1 := hstat (1,true)
  have h2 := hstat (2,true)
  have h3 := hstat (0,true)
  have h4 := hstat (1,false)
  have h5 := hstat (2,false)
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool,
    nextState, phaseAwarePolicy, nextPhase, start] at h0 h1 h2 h3 h4 h5
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three,
    Fintype.sum_bool] at hsum
  change v start = _ ∧ v (1,true) = _ ∧ v (2,true) = _ ∧
    v (0,true) = _ ∧ v (1,false) = _ ∧ v (2,false) = _
  constructor <;> linarith [h0, h1, h2, h3, h4, h5, hsum]


end PermanssonResearch.ReverseSolver.NonlinearPeriodThree
