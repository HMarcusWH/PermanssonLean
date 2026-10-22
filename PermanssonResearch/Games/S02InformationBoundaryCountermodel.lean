import PermanssonResearch.StrategicWorld.ActionTrace
import Mathlib.Tactic

/-!
# S-02: nonanticipating first-stage action cannot read an independent coin

A current own-action row in the original action-trace semantics is drawn
BEFORE the opponent's fresh independent uniform Boolean action. Any such
row has match success exactly 1/2. The hypothetical rule a := b after
observing that current draw instead succeeds with probability one and is
not an admissible original behavioral policy. This is a finite information
boundary, not an unrestricted full-strategy verification theorem.
-/

namespace PermanssonResearch.ActionTrace.S02InformationBoundary
open PermanssonResearch.ActionTrace
set_option autoImplicit false

def matchingPayoff (a b : Bool) : ℝ :=
  if a = b then 1 else 0

def independentFairMatch (a : Bool) : ℝ :=
  (matchingPayoff a false + matchingPayoff a true) / 2

theorem each_fixed_action_half (a : Bool) :
    independentFairMatch a = (1 / 2 : ℝ) := by
  cases a <;> norm_num [independentFairMatch, matchingPayoff]

/-- Every history-conditioned (but current-noise-blind) own probability row
has exactly one-half chance of matching the new independent opponent coin. -/
theorem every_nonanticipating_row_half (p : Row Bool) :
    p.expect independentFairMatch = (1 / 2 : ℝ) := by
  have he : independentFairMatch = (fun _ : Bool => (1 / 2 : ℝ)) := by
    funext a
    exact each_fixed_action_half a
  rw [he]
  exact Row.expect_const p (1 / 2 : ℝ)

/-- Looking at the independent draw first changes the information class. -/
theorem clairvoyant_match_one (b : Bool) :
    matchingPayoff b b = (1 : ℝ) := by
  simp [matchingPayoff]

theorem clairvoyant_not_a_nonanticipating_row (p : Row Bool) :
    p.expect independentFairMatch ≠ (1 : ℝ) := by
  rw [every_nonanticipating_row_half]
  norm_num

theorem explicit_information_advantage (p : Row Bool) :
    p.expect independentFairMatch < matchingPayoff true true := by
  rw [every_nonanticipating_row_half, clairvoyant_match_one]
  norm_num

end PermanssonResearch.ActionTrace.S02InformationBoundary
