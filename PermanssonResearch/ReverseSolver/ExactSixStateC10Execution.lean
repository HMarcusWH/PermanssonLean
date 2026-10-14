import PermanssonResearch.ReverseSolver.ComputableSixStateFixtures
import PermanssonResearch.ReverseSolver.RationalAbsorptionSolve
import PermanssonResearch.ReverseSolver.ExecutableConstitutiveSelection
import PermanssonResearch.MultipleLimit.ExactSixStateObservedGR
import PermanssonResearch.MultipleLimit.ExactSixStateConstitution
import Mathlib.Tactic

/-!
# C10 — exact six-state numerical test of the generic reference algorithm

Indices in this numerical query are frozen BEFORE evaluation:
0=full disruption, 1=half, 2=tiny, 3=identity, 4=u-only, 5=B-only.
The intended original comparison states are u=1 and a0=2.
The original Exact GR, B1, descriptor and genuine typed interventions
remain the unchanged previous-source objects.

Numeric `decide` checks validate exact Fraction/ℚ arithmetic,
not a missing general numerical/canonical path-law correspondence.
-/
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false
-- Exact reflection on six-state rational Floyd–Warshall graphs is deeper
-- than default kernel recursion; increase the bound without native_decide
-- or an extra axiom. Keep this option scoped to the C10 witness module.
set_option maxRecDepth 8192
set_option maxHeartbeats 0

open PermanssonResearch.MultipleLimit.ExactSixState
open PermanssonResearch.MultipleLimit.ExactSixStateCanonical
open PermanssonResearch.MultipleLimit.ExactSixStateObservedGR
open PermanssonResearch.MultipleLimit.ExactSixStateConstitution
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization

/-- Every matrix is directly computable and exactly row-stochastic. -/
def sixMenuMatrix (i : Fin 6) : RationalMarkovMatrix 6 :=
  if i = 0 then fullMatrixExecutable
  else if i = 1 then halfMatrixExecutable
  else if i = 2 then tinyMatrixExecutable
  else if i = 3 then sixStateMatrix
  else if i = 4 then uOnlyMatrixExecutable
  else bOnlyMatrixExecutable

/-- A function-valued raw exact input. This is already numerically indexed;
external JSON deserialization is NOT proven here. -/
def sixRaw : RawInput 6 6 where
  baseline := sixStateMatrix.entry
  members := fun i => (sixMenuMatrix i).entry
  descriptor := observedRecurrent
  comparison := {1, 2}

/-- Proof-carrying checked input keeps exactly the given rows. -/
def sixChecked : CheckedInput sixRaw where
  statesPositive := by decide
  menuPositive := by decide
  comparisonNonempty := by simp [sixRaw]
  baseline := sixStateMatrix
  members := sixMenuMatrix
  baselineExact := by intro x y; rfl
  membersExact := by intro i x y; rfl

/-- Physical recurrent sets, fixed independently of the numerical solver.
The baseline has two true recurrent classes; an introduced absorbing u
is false-labelled. These are *proposed receipt data*, whose correctness
is checked against the actual matrices below. -/
def sixA : Finset (Fin 6) := {2, 3}
def sixB : Finset (Fin 6) := {4, 5}
def sixU : Finset (Fin 6) := {1}

/-- Canonical exact baseline A-class selection weights. -/
def sixAWeight (x : Fin 6) : ℚ :=
  if x = 0 ∨ x = 1 then 1 / 3
  else if x = 2 ∨ x = 3 then 1
  else 0

def sixBaselineCertificate : DirichletCertificate 6 where
  classes := {sixA, sixB}
  weight := fun C x =>
    if C = sixA then sixAWeight x
    else if C = sixB then 1 - sixAWeight x
    else 0

/-- If the false U absorber is installed, epsilon is the exact
one-step probability that a0 enters U, while t/u already end in U. -/
def sixUWeight (ε : ℚ) (x : Fin 6) : ℚ :=
  if x = 0 ∨ x = 1 then 1
  else if x = 2 ∨ x = 3 then ε
  else 0

def sixSplitCertificate (ε : ℚ) : DirichletCertificate 6 where
  classes := {sixU, sixB}
  weight := fun C x =>
    if C = sixU then sixUWeight ε x
    else if C = sixB then 1 - sixUWeight ε x
    else 0

/-- The u-only response preserves class A as a separate true-labelled
periodic class. B-only has one true bottom class with absorption one. -/
def sixUOnlyCertificate : DirichletCertificate 6 where
  classes := {sixU, sixA, sixB}
  weight := fun C x =>
    if C = sixU then (if x = 0 ∨ x = 1 then 1 else 0)
    else if C = sixA then (if x = 2 ∨ x = 3 then 1 else 0)
    else if C = sixB then (if x = 4 ∨ x = 5 then 1 else 0)
    else 0

def sixBOnlyCertificate : DirichletCertificate 6 where
  classes := {sixB}
  weight := fun C _ => if C = sixB then 1 else 0

/-- Computably checkable *literal exact rational receipts*. Unlike a
brute-force six-by-six adjugate reduction, these values can be checked
against the generic harmonic/boundary equation checker without making
the Python or hand-derived answer a theorem premise. -/
def sixReference : MenuCertificate 6 6 where
  baseline := sixBaselineCertificate
  members := fun i =>
    if i = 0 then sixSplitCertificate 1
    else if i = 1 then sixSplitCertificate (1/2)
    else if i = 2 then sixSplitCertificate (1/1000)
    else if i = 3 then sixBaselineCertificate
    else if i = 4 then sixUOnlyCertificate
    else sixBOnlyCertificate

/-- Original comparison states have an exact rational index representation;
all states of the frozen original B1 are included. -/
theorem sixComparison_complete (x : Fin 6) :
    x ∈ sixRaw.comparison ↔
      decode x ∈ comparison.states := by
  rw [comparison_states]
  simp [sixRaw, decode, Finset.mem_insert, Finset.mem_singleton]

/-- The globally frozen Boolean descriptor has not been modified for
intervention-side states. -/
theorem sixDescriptor_frozen (x : Fin 6) :
    observedDescriptor (decode x) = sixRaw.descriptor x := by
  rfl

/-- Compiler-executable exact calculations; the following theorems are
not assumed external Python values. -/
theorem sixReference_valid :
    checkMenu sixRaw sixChecked sixReference = true := by
  decide +kernel

theorem sixMargins_exact :
    numericalMargin sixRaw sixChecked sixReference (0 : Fin 6) = 1 ∧
    numericalMargin sixRaw sixChecked sixReference (1 : Fin 6) = (1/2 : ℚ) ∧
    numericalMargin sixRaw sixChecked sixReference (2 : Fin 6) = (1/1000 : ℚ) ∧
    numericalMargin sixRaw sixChecked sixReference (3 : Fin 6) = 0 ∧
    numericalMargin sixRaw sixChecked sixReference (4 : Fin 6) = 0 ∧
    numericalMargin sixRaw sixChecked sixReference (5 : Fin 6) = 0 := by
  decide +kernel

theorem sixBest_exact :
    bestMargin sixRaw sixChecked sixReference = 1 ∧
    selectBest sixRaw sixChecked sixReference = (0 : Fin 6) := by
  decide +kernel

end C10
end ReverseSolver
end PermanssonResearch