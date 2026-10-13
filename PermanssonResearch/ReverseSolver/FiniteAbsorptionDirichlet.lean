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
private theorem list_all_true_iff {α : Type*}
    (xs : List α) (p : α → Bool) :
    xs.all p = true ↔ ∀ a ∈ xs, p a = true := by
  induction xs with
  | nil => simp
  | cons a tail ih => simp [List.all, ih]

/-- No classical `Decidable` oracle: all propositions are checked by
explicit finite List enumeration and finite Fin-indexed decisions. -/
def checkDirichlet {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n) : Bool :=
  decide (cert.classes = bottomClasses K) &&
  cert.classes.toList.all (fun C =>
    decide (∀ x : Fin n,
      if x ∈ recurrentUnion cert then
        cert.weight C x = (if x ∈ C then 1 else 0)
      else cert.weight C x =
        ∑ y : Fin n, K.entry x y * cert.weight C y)) &&
  cert.classes.toList.all (fun C =>
    decide (∀ x : Fin n,
      0 ≤ cert.weight C x ∧ cert.weight C x ≤ 1)) &&
  decide (∀ x : Fin n,
    (∑ C ∈ cert.classes, cert.weight C x) = 1)

/-- True checker output entails every stated exact algebraic obligation. -/
theorem checkDirichlet_sound {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (h : checkDirichlet K cert = true) :
    DirichletConditions K cert := by
  unfold checkDirichlet at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hclass, hboundary⟩, hbounds⟩, htotal⟩
  have hclass' : cert.classes = bottomClasses K := by
    simpa only [decide_eq_true_eq] using hclass
  have htotal' : ∀ x : Fin n,
      (∑ C ∈ cert.classes, cert.weight C x) = 1 := by
    simpa only [decide_eq_true_eq] using htotal
  refine ⟨hclass', ?_, ?_, htotal'⟩
  · intro C hC x
    have hCList : C ∈ cert.classes.toList := by simpa using hC
    have hCase :=
      (list_all_true_iff cert.classes.toList (fun D =>
        decide (∀ z : Fin n,
          if z ∈ recurrentUnion cert then
            cert.weight D z = (if z ∈ D then 1 else 0)
          else cert.weight D z =
            ∑ w : Fin n, K.entry z w * cert.weight D w))).mp
        hboundary C hCList
    have hAll : ∀ z : Fin n,
        if z ∈ recurrentUnion cert then
          cert.weight C z = (if z ∈ C then 1 else 0)
        else cert.weight C z =
          ∑ w : Fin n, K.entry z w * cert.weight C w := by
      simpa only [decide_eq_true_eq] using hCase
    exact hAll x
  · intro C hC x
    have hCList : C ∈ cert.classes.toList := by simpa using hC
    have hCase :=
      (list_all_true_iff cert.classes.toList (fun D =>
        decide (∀ z : Fin n,
          0 ≤ cert.weight D z ∧ cert.weight D z ≤ 1))).mp
        hbounds C hCList
    have hAll : ∀ z : Fin n,
        0 ≤ cert.weight C z ∧ cert.weight C z ≤ 1 := by
      simpa only [decide_eq_true_eq] using hCase
    exact hAll x

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