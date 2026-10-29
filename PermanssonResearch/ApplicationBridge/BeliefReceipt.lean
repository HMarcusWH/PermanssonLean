import PermanssonResearch.ApplicationBridge.FiniteWorldInput
import Mathlib.Tactic

/-!
# ApplicationBridge — observation-before-action finite belief receipt

The successor's finite belief-tree profile first samples an observation of the
CURRENT world state, then selects a control measurable with respect to that
observation/history, then applies P followed by U. This differs from the
`ReverseSolver.Belief` convention in which an observation is sampled after
an action and state transition. No equality of the two chronologies is assumed.

These proofs certify the algebra of the one-step observed law for a supplied
finite rational model and a policy indexed by observed `o`. They do NOT prove
that an arbitrary JSON receipt has been parsed as the exact Lean values, that
a control is admissible, or that the claimed multi-stage optimum is global.
-/

namespace PermanssonResearch.ApplicationBridge

set_option autoImplicit false

/-- Finite joint-state belief, normalized over all strategic/world pairs. -/
structure RationalBelief (ns nx : ℕ) where
  weight : (Fin ns × Fin nx) → ℚ
  nonneg : ∀ y, 0 ≤ weight y
  sum_one : (∑ y : Fin ns × Fin nx, weight y) = 1

namespace RationalBelief
variable {ns nx : ℕ}

def dot (b : RationalBelief ns nx) (v : (Fin ns × Fin nx) → ℚ) : ℚ :=
  ∑ y : Fin ns × Fin nx, b.weight y * v y

end RationalBelief

/-- Likelihoods are indexed by the PRE-action world state and observation. -/
structure RationalObservationInput (ns nx na no : ℕ) where
  worldInput : FiniteWorldInput ns nx na
  likelihood : Fin nx → Fin no → ℚ
  likelihood_nonneg : ∀ x o, 0 ≤ likelihood x o
  likelihood_sum_one : ∀ x, (∑ o : Fin no, likelihood x o) = 1

namespace RationalObservationInput
variable {ns nx na no : ℕ} (m : RationalObservationInput ns nx na no)

def observedAtom (b : RationalBelief ns nx) (o : Fin no)
    (y : Fin ns × Fin nx) : ℚ :=
  b.weight y * m.likelihood y.2 o

def observationMass (b : RationalBelief ns nx) (o : Fin no) : ℚ :=
  ∑ y : Fin ns × Fin nx, m.observedAtom b o y

theorem observedAtom_nonneg (b : RationalBelief ns nx) (o : Fin no)
    (y : Fin ns × Fin nx) : 0 ≤ m.observedAtom b o y :=
  mul_nonneg (b.nonneg y) (m.likelihood_nonneg y.2 o)

theorem observationMass_nonneg (b : RationalBelief ns nx) (o : Fin no) :
    0 ≤ m.observationMass b o :=
  Finset.sum_nonneg (fun y _ => m.observedAtom_nonneg b o y)

/-- The observed-current-state law is normalized, including zero-mass
    observations. -/
theorem observationMass_sum_one (b : RationalBelief ns nx) :
    (∑ o : Fin no, m.observationMass b o) = 1 := by
  simp only [observationMass, observedAtom]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, m.likelihood_sum_one, mul_one]
  exact b.sum_one

theorem observedAtom_zero_of_zero_mass (b : RationalBelief ns nx) (o : Fin no)
    (hz : m.observationMass b o = 0) (y : Fin ns × Fin nx) :
    m.observedAtom b o y = 0 := by
  have hle : m.observedAtom b o y ≤ m.observationMass b o :=
    Finset.single_le_sum (fun z _ => m.observedAtom_nonneg b o z)
      (Finset.mem_univ y)
  exact le_antisymm (hz ▸ hle) (m.observedAtom_nonneg b o y)

/-- Bayes posterior. A zero-mass branch uses the original belief as a
    deliberately unobservable default, rather than introducing fake mass. -/
noncomputable def posterior (b : RationalBelief ns nx) (o : Fin no) :
    RationalBelief ns nx := by
  classical
  by_cases hz : m.observationMass b o = 0
  · exact b
  · refine {
      weight := fun y => m.observedAtom b o y / m.observationMass b o
      nonneg := fun y => div_nonneg (m.observedAtom_nonneg b o y)
        (m.observationMass_nonneg b o)
      sum_one := ?_ }
    change (∑ y : Fin ns × Fin nx,
      m.observedAtom b o y / m.observationMass b o) = 1
    rw [← Finset.sum_div]
    exact div_self hz

theorem posterior_formula (b : RationalBelief ns nx) (o : Fin no)
    (hz : m.observationMass b o ≠ 0) (y : Fin ns × Fin nx) :
    (m.posterior b o).weight y =
      m.observedAtom b o y / m.observationMass b o := by
  simp [posterior, hz]

/-- This cancellation holds even on impossible observation branches.
    A zero-mass observation cannot change a weighted calculation. -/
theorem posterior_cancel (b : RationalBelief ns nx) (o : Fin no)
    (y : Fin ns × Fin nx) :
    m.observationMass b o * (m.posterior b o).weight y =
      m.observedAtom b o y := by
  classical
  by_cases hz : m.observationMass b o = 0
  · rw [hz, zero_mul, m.observedAtom_zero_of_zero_mass b o hz y]
  · rw [m.posterior_formula b o hz y]
    exact mul_div_cancel₀ _ hz

theorem posterior_dot_cancel (b : RationalBelief ns nx) (o : Fin no)
    (v : (Fin ns × Fin nx) → ℚ) :
    m.observationMass b o * (m.posterior b o).dot v =
      ∑ y : Fin ns × Fin nx, m.observedAtom b o y * v y := by
  simp only [RationalBelief.dot, Finset.mul_sum, ← mul_assoc, m.posterior_cancel]

/-- A controller sees only the current observation `o`, not the hidden
    joint state `y`. A positive-probability observation must select an action
    feasible at *every* hidden state with positive conditional mass. Unreachable
    observations are intentionally exempt, as in the Python numeric scope. -/
structure LegalObservedChoice (b : RationalBelief ns nx) where
  choose : Fin no → Fin na
  legal : ∀ o y, m.observationMass b o ≠ 0 →
    (m.posterior b o).weight y ≠ 0 →
      m.worldInput.feasible y.1 y.2 (choose o)

/-- A controller selects one action as a function of its CURRENT observation.
    The world state `y` is not supplied to this controller. -/
def observedPolicyValue (b : RationalBelief ns nx) (choose : Fin no → Fin na)
    (terminal : (Fin ns × Fin nx) → ℚ) : ℚ :=
  ∑ o : Fin no, m.observationMass b o *
    (m.posterior b o).dot (fun y =>
      ∑ z : Fin ns × Fin nx,
        m.worldInput.controlledAtom (choose o) y z * terminal z)

/-- Unnormalized forward-sum formulation, independent of posterior division.
    Both are exact source α/P/U arithmetic under the declared chronology. -/
def unnormalizedPolicyValue (b : RationalBelief ns nx) (choose : Fin no → Fin na)
    (terminal : (Fin ns × Fin nx) → ℚ) : ℚ :=
  ∑ o : Fin no, ∑ y : Fin ns × Fin nx,
    m.observedAtom b o y *
      (∑ z : Fin ns × Fin nx,
        m.worldInput.controlledAtom (choose o) y z * terminal z)

/-- A receipt value computed by posterior recursion equals the independently
    expanded observation→action→P→U finite forward sum. This is not an
    assertion of policy optimality or of unrestricted intervention admissibility. -/
theorem observedPolicyValue_eq_unnormalized (b : RationalBelief ns nx)
    (choose : Fin no → Fin na) (terminal : (Fin ns × Fin nx) → ℚ) :
    m.observedPolicyValue b choose terminal =
      m.unnormalizedPolicyValue b choose terminal := by
  unfold observedPolicyValue unnormalizedPolicyValue
  apply Finset.sum_congr rfl
  intro o _
  exact m.posterior_dot_cancel b o (fun y =>
    ∑ z : Fin ns × Fin nx,
      m.worldInput.controlledAtom (choose o) y z * terminal z)

/-- The checked common-menu certificate constrains observability and
    feasibility without changing the exact Bayes/forward-law identity. -/
theorem legalChoice_value_consistency (b : RationalBelief ns nx)
    (choice : LegalObservedChoice m b)
    (terminal : (Fin ns × Fin nx) → ℚ) :
    m.observedPolicyValue b choice.choose terminal =
      m.unnormalizedPolicyValue b choice.choose terminal :=
  m.observedPolicyValue_eq_unnormalized b choice.choose terminal

/-- For a fixed observed action, the complete next-joint law has mass one. -/
theorem posterior_controlled_next_sum_one (b : RationalBelief ns nx)
    (o : Fin no) (a : Fin na) :
    (∑ z : Fin ns × Fin nx,
      ∑ y : Fin ns × Fin nx,
        (m.posterior b o).weight y * m.worldInput.controlledAtom a y z) = 1 := by
  calc
    (∑ z : Fin ns × Fin nx,
      ∑ y : Fin ns × Fin nx,
        (m.posterior b o).weight y * m.worldInput.controlledAtom a y z) =
        ∑ y : Fin ns × Fin nx, (m.posterior b o).weight y *
          (∑ z : Fin ns × Fin nx, m.worldInput.controlledAtom a y z) := by
            rw [Finset.sum_comm]
            simp only [Finset.mul_sum]
    _ = ∑ y : Fin ns × Fin nx, (m.posterior b o).weight y := by
          simp only [m.worldInput.controlledAtom_sum_one, mul_one]
    _ = 1 := (m.posterior b o).sum_one

end RationalObservationInput
end PermanssonResearch.ApplicationBridge
