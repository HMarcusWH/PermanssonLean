import PermanssonResearch.X1.Parameters

/-!
# X1: finite rational Poisson certificates

This module proves only exact rational identities. `OccupationTargets` must
connect every entry to the actual alpha/P/U induced kernel before these
identities imply any invariant-law or canonical occupation conclusion.
The Boolean mode flag is false for E and true for L; it is not a new generator.
-/

namespace PermanssonResearch.X1.OccupationNumerics

set_option autoImplicit false

def rates (learner : Bool) (y : Y) : ℚ × ℚ :=
  if learner then (learnerExtract y.1.1, learnerExtract y.1.2)
  else (piExtract y.2, piExtract y.2)

def next (learner : Bool) (y : Y) (a : Action) : Memory :=
  if learner then updateL y a else y.1

/-- The rational alpha/P/U row, with the next world atom summed exactly.
This is an independently certified formula until the actual-kernel bridge. -/
def entry (learner : Bool) (y z : Y) : ℚ :=
  ∑ a : Action, boolMass (rates learner y).1 a.1 * boolMass (rates learner y).2 a.2 *
    boolMass (pRep y.2 a) z.2 * if next learner y a = z.1 then 1 else 0

def target (learner : Bool) : ℚ :=
  if learner then 44984685451641390245 / 355006278148174557117 else 5 / 12

/-- Exact symmetric bias, including the two transient actual states. -/
def learnerBias (y : Y) : ℚ :=
  let lo := min y.1.1.val y.1.2.val
  let hi := max y.1.1.val y.1.2.val
  if lo = 0 then
    if hi = 0 then
      if y.2 then 18536880168967027339580 / 6745119284815316585223
      else 834232478833826944200 / 2248373094938438861741
    else if hi = 1 then
      if y.2 then 15840683281493208845465 / 6745119284815316585223
      else 323475328327310089470 / 2248373094938438861741
    else
      if y.2 then 142848561496669483491113 / 67451192848153165852230
      else -226150755438709482810 / 2248373094938438861741
  else if lo = 1 then
    if hi = 1 then
      if y.2 then 14444140710994482746480 / 6745119284815316585223 else 0
    else
      if y.2 then 13126041884208197680520 / 6745119284815316585223
      else -224693274673831558920 / 2248373094938438861741
  else
    if y.2 then 11831364758483355705440 / 6745119284815316585223
    else -304354666295696534880 / 2248373094938438861741

def bias (learner : Bool) (y : Y) : ℚ :=
  if learner then learnerBias y else (5 / 3) * indicator y.2

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- Exhaustive exact rational certificate on ALL eighteen typed states,
including transient replete states. No stationary distribution is assumed. -/
theorem poisson_identity : ∀ (learner : Bool) (y : Y),
    bias learner y - ∑ z : Y, entry learner y z * bias learner z =
      indicator y.2 - target learner := by
  decide +kernel

end PermanssonResearch.X1.OccupationNumerics
