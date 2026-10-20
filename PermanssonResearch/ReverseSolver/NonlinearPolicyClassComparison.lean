import PermanssonResearch.ReverseSolver.NonlinearBooleanClassFunctional
import Mathlib.Tactic

/-!
NEXT-06.2: source-coupled native S=Fin3, X=A=Bool phase orbit and the
declared deterministic phase-BLIND class. The native finite orbit is
directly identified with the pre-existing exact Boolean-tail score.

These are NOT yet the original infinite-path expected nonlinear occupation
functional: relating its actual canonical empirical limit to the classwise
probabilities is a separate formal proof obligation.
-/
namespace PermanssonResearch.ReverseSolver.NonlinearPeriodThree

open PermanssonResearch.ReverseSolver.NonlinearOccupationBoundary

/-- The real native model has phase memory. Each step is induced by its
fixed physical and strategic-update rules. -/
def nativeOrbit (policy : State → Bool) : ℕ → State
  | 0 => start
  | n+1 => nextState policy (nativeOrbit policy n)

theorem native_phase_aware_initial_cycle :
    nativeOrbit phaseAwarePolicy 0 = start ∧
    nativeOrbit phaseAwarePolicy 1 = (1, true) ∧
    nativeOrbit phaseAwarePolicy 2 = (2, true) ∧
    nativeOrbit phaseAwarePolicy 3 = start := by
  decide

/-- Under the exact same native alpha-P-U physical P and U, a
phase-blind controller's physical coordinate follows the old Boolean
recurrence for every n, not merely for the first three samples. -/
theorem native_phase_blind_world_eq
    (policy : Bool → Bool) (n : ℕ) :
    (nativeOrbit (phaseBlindPolicy policy) n).2 =
      NonlinearOccupationBoundary.stationaryOrbit policy n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [nativeOrbit, nextState, phaseBlindPolicy,
        NonlinearOccupationBoundary.stationaryOrbit,
        NonlinearOccupationBoundary.forceAction]
      exact congrArg policy ih

def nativePhaseBlindTailShare (policy : Bool → Bool) : ℚ :=
    ((if (nativeOrbit (phaseBlindPolicy policy) 2).2 then (1:ℚ) else 0) +
     (if (nativeOrbit (phaseBlindPolicy policy) 3).2 then (1:ℚ) else 0))/2

theorem native_phase_blind_tail_share_eq (policy : Bool → Bool) :
    nativePhaseBlindTailShare policy =
      NonlinearOccupationBoundary.stationaryTrueShare policy := by
  unfold nativePhaseBlindTailShare NonlinearOccupationBoundary.stationaryTrueShare
  rw [native_phase_blind_world_eq policy 2, native_phase_blind_world_eq policy 3]

theorem native_phase_blind_tail_score_le_five_sixths
    (policy : Bool → Bool) :
    booleanRationalScore (nativePhaseBlindTailShare policy) ≤ 5/6 := by
  rw [native_phase_blind_tail_share_eq]
  exact NonlinearOccupationBoundary.deterministic_stationary_bound policy

/-- Exact native period-three true occupation on its actual cycle,
not a statement about arbitrary unobserved policies. -/
def nativePeriodThreeShare : ℚ :=
    ((if (nativeOrbit phaseAwarePolicy 0).2 then (1:ℚ) else 0) +
     (if (nativeOrbit phaseAwarePolicy 1).2 then (1:ℚ) else 0) +
     (if (nativeOrbit phaseAwarePolicy 2).2 then (1:ℚ) else 0))/3

theorem native_period_three_share : nativePeriodThreeShare = 2/3 := by
  norm_num [nativePeriodThreeShare, nativeOrbit, start, phaseAwarePolicy,
    nextState, nextPhase]

theorem native_period_three_finite_score_one :
    booleanRationalScore nativePeriodThreeShare = 1 := by
  rw [native_period_three_share]
  exact randomized_tie_score

theorem native_phase_aware_strictly_beats_phase_blind_finite_orbits
    (policy : Bool → Bool) :
    booleanRationalScore (nativePhaseBlindTailShare policy) <
      booleanRationalScore nativePeriodThreeShare := by
  rw [native_period_three_finite_score_one]
  exact lt_of_le_of_lt
    (native_phase_blind_tail_score_le_five_sixths policy) (by norm_num)

/-- There is no unrestricted winner: a randomized Bool-only controller
with stationary true mass 2/3 can tie the score. The exact probability
realization is kept as an independent acceptance obligation. -/
theorem no_universal_strict_score_gap :
    ¬ ∀ p : ℚ, (0 ≤ p ∧ p ≤ 1) →
      booleanRationalScore p < booleanRationalScore nativePeriodThreeShare := by
  intro h
  have hp := h (2/3) (by constructor <;> norm_num)
  rw [native_period_three_finite_score_one, randomized_tie_score] at hp
  exact (lt_irrefl (1 : ℚ)) hp

end PermanssonResearch.ReverseSolver.NonlinearPeriodThree
