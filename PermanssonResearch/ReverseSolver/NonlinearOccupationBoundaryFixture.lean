import Mathlib.Tactic

/-!
# D2-P09 / D-09 — two-state nonlinear occupation countermodel

The physical update is the chosen action. Every deterministic stationary
controller is an arbitrary map Bool → Bool. Its orbit from the fixed false
start is eventually period ≤ 2. A precommitted nonstationary schedule
(true,true,false) is state-independent and has period 3.

The fixed nonlinear score is F(p)=1-|p-2/3|. This module proves the
actual finite-period orbit arithmetic and no-stationary-score-one
counterexample. It does NOT prove an arbitrary infinite-path occupation-law
correspondence, or unrestricted all-history optimization.
-/

namespace PermanssonResearch.ReverseSolver.NonlinearOccupationBoundary

set_option autoImplicit false

def forceAction (_state action : Bool) : Bool := action

def stationaryOrbit (policy : Bool → Bool) : ℕ → Bool
  | 0 => false
  | n+1 => forceAction (stationaryOrbit policy n) (policy (stationaryOrbit policy n))

/-- Actual stationary Boolean orbit is eventually two-periodic. -/
theorem stationary_orbit_two_periodic (policy : Bool → Bool) (n : ℕ) :
    stationaryOrbit policy (n+4) = stationaryOrbit policy (n+2) := by
  induction n with
  | zero =>
    cases h0 : policy false <;> cases h1 : policy true <;>
      simp [stationaryOrbit, forceAction, h0, h1]
  | succ n ih =>
    simpa only [Nat.succ_add, stationaryOrbit, forceAction] using congrArg policy ih

def stationaryTrueShare (policy : Bool → Bool) : ℚ :=
  ((if stationaryOrbit policy 2 then (1 : ℚ) else 0) +
   (if stationaryOrbit policy 3 then (1 : ℚ) else 0)) / 2

/-- Fixed descriptor score, not chosen after observing a favorable outcome. -/
def score (share : ℚ) : ℚ := 1 - |share - 2/3|

/-- All four deterministic stationary Boolean feedback maps are covered. -/
theorem deterministic_stationary_bound (policy : Bool → Bool) :
    score (stationaryTrueShare policy) ≤ 5/6 := by
  cases h0 : policy false <;> cases h1 : policy true <;>
    norm_num [score, stationaryTrueShare, stationaryOrbit, forceAction, h0, h1]

def alternatingFeedback : Bool → Bool := fun x => !x

theorem deterministic_stationary_optimum_attained :
    score (stationaryTrueShare alternatingFeedback) = 5/6 := by
  norm_num [score, stationaryTrueShare, alternatingFeedback, stationaryOrbit, forceAction]

/-- State-independent three-period control, selected before any observation. -/
def periodicAction (n : ℕ) : Bool := n % 3 != 2

def periodicOrbit : ℕ → Bool
  | 0 => false
  | n+1 => forceAction (periodicOrbit n) (periodicAction n)

theorem periodic_controller_blocks (k : ℕ) :
    periodicAction (3*k) = true ∧
    periodicAction (3*k+1) = true ∧
    periodicAction (3*k+2) = false := by
  simp [periodicAction, Nat.mul_mod, Nat.add_mod]

theorem first_three_physical_states :
    periodicOrbit 1 = true ∧ periodicOrbit 2 = true ∧ periodicOrbit 3 = false := by
  decide

def nonstationaryThreeStepShare : ℚ :=
  ((if periodicOrbit 1 then (1 : ℚ) else 0) +
   (if periodicOrbit 2 then (1 : ℚ) else 0) +
   (if periodicOrbit 3 then (1 : ℚ) else 0)) / 3

theorem period_three_true_share : nonstationaryThreeStepShare = 2/3 := by
  norm_num [nonstationaryThreeStepShare, periodicOrbit, periodicAction, forceAction]

theorem period_three_score_one : score nonstationaryThreeStepShare = 1 := by
  rw [period_three_true_share]
  norm_num [score]

/-- A concrete nonlinear policy-class counterexample, not an unproved
all-history asymptotic claim. -/
theorem period_three_beats_all_stationary (policy : Bool → Bool) :
    score (stationaryTrueShare policy) < score nonstationaryThreeStepShare := by
  rw [period_three_score_one]
  exact lt_of_le_of_lt (deterministic_stationary_bound policy) (by norm_num)

end PermanssonResearch.ReverseSolver.NonlinearOccupationBoundary
