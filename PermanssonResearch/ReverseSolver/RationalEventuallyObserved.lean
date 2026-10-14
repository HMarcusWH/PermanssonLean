import PermanssonResearch.ReverseSolver.FiniteAbsorptionDirichlet
import Mathlib.Tactic

/-!
# C10 — exact eventual-true numerical value from class absorption

A good class has EVERY member Boolean-labelled true. Mixed recurrent
classes are not good, even if some members receive positive stationary
occupation. The actual infinite-path equivalence is a separate proof gate.
-/
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- The descriptor is globally frozen, including on states reachable only
after an intervention. -/
def GoodClass {n : ℕ} (h : Fin n → Bool) (C : Finset (Fin n)) : Prop :=
  ∀ x ∈ C, h x = true


/-- A constructive decision procedure for the finite Boolean descriptor
of every state in a proposed recurrent class. -/
private instance goodClass_decidable {n : ℕ}
    (h : Fin n → Bool) (C : Finset (Fin n)) :
    Decidable (GoodClass h C) := by
  unfold GoodClass
  infer_instance

/-- Exact rational event value determined by the supplied absorption table. -/
def eventValue {n : ℕ}
    (cert : DirichletCertificate n) (h : Fin n → Bool) (x : Fin n) : ℚ :=
  ∑ C ∈ cert.classes.filter (GoodClass h), cert.weight C x

theorem goodClass_iff {n : ℕ} (h : Fin n → Bool)
    (C : Finset (Fin n)) : GoodClass h C ↔ ∀ x ∈ C, h x = true := Iff.rfl

/-- Exact nonnegative class masses yield a nonnegative eventual-true value;
this is an algebraic output bound, not a new path-law certificate. -/
theorem checked_eventValue_nonneg {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (hcert : checkDirichlet K cert = true)
    (h : Fin n → Bool) (x : Fin n) :
    0 ≤ eventValue cert h x := by
  unfold eventValue
  apply Finset.sum_nonneg
  intro C hC
  have hmember : C ∈ cert.classes := (Finset.mem_filter.mp hC).1
  exact (checked_weight_bounds K cert hcert C hmember x).1

end C10
end ReverseSolver
end PermanssonResearch