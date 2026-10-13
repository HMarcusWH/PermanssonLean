import PermanssonResearch.ReverseSolver.RationalRecurrentAccess
import PermanssonResearch.ReverseSolver.FiniteAbsorptionDirichlet
import Mathlib.Tactic

/-!
# C10 — accepted exact rational absorption receipts are unique

Two accepted Dirichlet certificates for one fixed rational Markov matrix
carry exactly the same bottom-class list and identical absorption weights
for every listed class and every physical state. The proof invokes the
already-certified finite-state maximum principle and the source-specific
native recurrent-access theorem. It neither assumes an external probabilistic
identity nor equates numeric values with canonical infinite-path probabilities.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- Any two exact checker-accepted rational class columns coincide; neither
model status nor a hypothesis equating numerical and path-law values is used. -/
theorem checked_class_column_unique {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n)
    (a b : DirichletCertificate n)
    (ha : checkDirichlet K a = true)
    (hb : checkDirichlet K b = true)
    (C : Finset (Fin n)) (hC : C ∈ bottomClasses K) :
    ∀ x : Fin n, a.weight C x = b.weight C x := by
  have hA := checkDirichlet_sound K a ha
  have hB := checkDirichlet_sound K b hb
  have hCA : C ∈ a.classes := by rw [hA.1]; exact hC
  have hCB : C ∈ b.classes := by rw [hB.1]; exact hC
  have hRA : recurrentUnion a = rationalRecurrentUnion K := by
    simp [recurrentUnion, rationalRecurrentUnion, hA.1]
  have hRB : recurrentUnion b = rationalRecurrentUnion K := by
    simp [recurrentUnion, rationalRecurrentUnion, hB.1]
  have hA_boundary (x : Fin n) (hx : x ∈ rationalRecurrentUnion K) :
      a.weight C x = (if x ∈ C then 1 else 0) := by
    have h := hA.2.1 C hCA x
    simpa [hRA, hx] using h
  have hB_boundary (x : Fin n) (hx : x ∈ rationalRecurrentUnion K) :
      b.weight C x = (if x ∈ C then 1 else 0) := by
    have h := hB.2.1 C hCB x
    simpa [hRB, hx] using h
  have hA_transient (x : Fin n) (hx : x ∉ rationalRecurrentUnion K) :
      a.weight C x = ∑ y : Fin n, K.entry x y * a.weight C y := by
    have h := hA.2.1 C hCA x
    simpa [hRA, hx] using h
  have hB_transient (x : Fin n) (hx : x ∉ rationalRecurrentUnion K) :
      b.weight C x = ∑ y : Fin n, K.entry x y * b.weight C y := by
    have h := hB.2.1 C hCB x
    simpa [hRB, hx] using h
  have hEq : a.weight C = b.weight C :=
    rationalBSCC_dirichlet_unique K (a.weight C) (b.weight C)
      (fun x hx => (hA_boundary x hx).trans (hB_boundary x hx).symm)
      hA_transient hB_transient
  intro x
  exact congrFun hEq x

/-- All accepted class columns and the exact bottom class list agree.
This is stronger than agreement of one declared transition-corridor score. -/
theorem checked_dirichlet_tables_unique {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n)
    (a b : DirichletCertificate n)
    (ha : checkDirichlet K a = true)
    (hb : checkDirichlet K b = true) :
    a.classes = b.classes ∧
      ∀ C ∈ a.classes, ∀ x : Fin n, a.weight C x = b.weight C x := by
  have hA := checkDirichlet_sound K a ha
  have hB := checkDirichlet_sound K b hb
  refine ⟨hA.1.trans hB.1.symm, ?_⟩
  intro C hC
  exact checked_class_column_unique K a b ha hb C (by
    rw [← hA.1]
    exact hC)

end C10
end ReverseSolver
end PermanssonResearch