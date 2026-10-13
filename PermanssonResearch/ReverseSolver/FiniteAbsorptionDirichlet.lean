import PermanssonResearch.ReverseSolver.RationalBSCC
import Mathlib.Tactic

/-!
# C10 — exact rational boundary-value certificates

The certificate checker is algebraic. It checks the full list of computed
classes, all Dirichlet boundary/harmonic equations, boundedness, and that
the class weights sum to one at every state. A separate probabilistic
uniqueness theorem is required to identify these checked vectors with
canonical infinite-path absorption probabilities.
-/
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- A numerical table of class-specific exact rational absorption weights. -/
structure DirichletCertificate (n : ℕ) where
  classes : Finset (Finset (Fin n))
  weight : Finset (Fin n) → Fin n → ℚ

/-- States belonging to any claimed bottom recurrent class. -/
def recurrentUnion {n : ℕ} (cert : DirichletCertificate n) : Finset (Fin n) :=
  cert.classes.biUnion (fun C => C)

/-- Explicit finite rational equations. The first conjunct also ensures
there are no omitted/duplicated classes relative to the executable graph
proposal; this is NOT yet a theorem about the abstract canonical selector. -/
def DirichletConditions {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n) : Prop :=
  cert.classes = bottomClasses K ∧
  (∀ C ∈ cert.classes, ∀ x : Fin n,
    if x ∈ recurrentUnion cert then
      cert.weight C x = (if x ∈ C then 1 else 0)
    else
      cert.weight C x = ∑ y : Fin n, K.entry x y * cert.weight C y) ∧
  (∀ C ∈ cert.classes, ∀ x : Fin n,
    0 ≤ cert.weight C x ∧ cert.weight C x ≤ 1) ∧
  (∀ x : Fin n, (∑ C ∈ cert.classes, cert.weight C x) = 1)

/-- Computable exact-Fraction/ℚ checker (no tolerances, time limits, or
external helper assumptions). -/
def checkDirichlet {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n) : Bool :=
  decide (cert.classes = bottomClasses K) &&
  cert.classes.all (fun C =>
    (Finset.univ : Finset (Fin n)).all (fun x =>
      decide (if x ∈ recurrentUnion cert then
        cert.weight C x = (if x ∈ C then 1 else 0)
      else cert.weight C x =
        ∑ y : Fin n, K.entry x y * cert.weight C y))) &&
  cert.classes.all (fun C =>
    (Finset.univ : Finset (Fin n)).all (fun x =>
      decide (0 ≤ cert.weight C x ∧ cert.weight C x ≤ 1))) &&
  (Finset.univ : Finset (Fin n)).all (fun x =>
    decide ((∑ C ∈ cert.classes, cert.weight C x) = 1))

/-- True checker output entails every stated exact algebraic obligation. -/
theorem checkDirichlet_sound {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (h : checkDirichlet K cert = true) :
    DirichletConditions K cert := by
  unfold checkDirichlet at h
  simp only [Bool.and_eq_true, Finset.all_eq_true,
    decide_eq_true_eq, Finset.mem_univ, forall_const] at h
  rcases h with ⟨hclasses, hboundary, hbounds, hsum⟩
  refine ⟨hclasses, ?_, ?_, ?_⟩
  · intro C hC x
    exact hboundary C hC x
  · intro C hC x
    exact hbounds C hC x
  · intro x
    exact hsum x

/-- Every checked column stays in [0,1], at every state. -/
theorem checked_weight_bounds {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (h : checkDirichlet K cert = true)
    (C : Finset (Fin n)) (hC : C ∈ cert.classes) (x : Fin n) :
    0 ≤ cert.weight C x ∧ cert.weight C x ≤ 1 :=
  (checkDirichlet_sound K cert h).2.2.1 C hC x

/-- Every checked state's destination probabilities add to exactly one. -/
theorem checked_class_mass_one {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (h : checkDirichlet K cert = true) (x : Fin n) :
    (∑ C ∈ cert.classes, cert.weight C x) = 1 :=
  (checkDirichlet_sound K cert h).2.2.2 x

end C10
end ReverseSolver
end PermanssonResearch