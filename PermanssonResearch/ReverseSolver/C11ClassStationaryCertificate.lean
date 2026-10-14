import PermanssonResearch.ReverseSolver.RationalBSCC
import Mathlib.Tactic

/-!
# C11-A — exact rational stationary certificate for a computed bottom class

The checker is finite and decidable. It accepts a NONEMPTY state universe,
the complete original finite kernel, a genuine bottom class, an all-state
stationary probability vector with support confined to that class, and the
full row-vector balance equation. No rational-to-typed identification, an
external JSON parser, or an executable solver is assumed in the certificate.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C11

set_option autoImplicit false

open C10

structure ClassStationaryCandidate (n : ℕ) where
  classStates : Finset (Fin n)
  weights : Fin n → ℚ

def ClassStationaryConditions {n : ℕ}
    (K : RationalMarkovMatrix n)
    (r : ClassStationaryCandidate n) : Prop :=
  0 < n ∧
  r.classStates ∈ bottomClasses K ∧
  (∀ x, 0 ≤ r.weights x) ∧
  (∑ x : Fin n, r.weights x) = 1 ∧
  (∀ x, x ∉ r.classStates → r.weights x = 0) ∧
  (∀ y, r.weights y =
    ∑ x : Fin n, r.weights x * K.entry x y)

def checkClassStationary {n : ℕ}
    (K : RationalMarkovMatrix n)
    (r : ClassStationaryCandidate n) : Bool :=
  decide (ClassStationaryConditions K r)

/-- An accepted receipt proves EVERY exact rational equation, including the
positive dimension and the computed-bottom-class membership condition. -/
theorem checkClassStationary_sound {n : ℕ}
    (K : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary K r = true) :
    ClassStationaryConditions K r := by
  exact of_decide_eq_true (show decide (ClassStationaryConditions K r) = true
    from hc)

/-- At n=0 no candidate can pass, even if its equations are vacuous. -/
theorem zero_dimension_rejected
    (K : RationalMarkovMatrix 0) (r : ClassStationaryCandidate 0) :
    checkClassStationary K r = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hp := (checkClassStationary_sound K r h).1
  omega

theorem checked_nonnegative {n : ℕ}
    (K : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary K r = true) :
    ∀ x, 0 ≤ r.weights x :=
  (checkClassStationary_sound K r hc).2.2.1

theorem checked_normalized {n : ℕ}
    (K : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary K r = true) :
    (∑ x : Fin n, r.weights x) = 1 :=
  (checkClassStationary_sound K r hc).2.2.2.1

theorem checked_supported {n : ℕ}
    (K : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary K r = true) :
    ∀ x, x ∉ r.classStates → r.weights x = 0 :=
  (checkClassStationary_sound K r hc).2.2.2.2.1

theorem checked_balance {n : ℕ}
    (K : RationalMarkovMatrix n) (r : ClassStationaryCandidate n)
    (hc : checkClassStationary K r = true) :
    ∀ y, r.weights y =
      ∑ x : Fin n, r.weights x * K.entry x y :=
  (checkClassStationary_sound K r hc).2.2.2.2.2

end C11
end ReverseSolver
end PermanssonResearch
