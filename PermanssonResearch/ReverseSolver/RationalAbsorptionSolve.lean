import PermanssonResearch.ReverseSolver.FiniteAbsorptionDirichlet
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# C10 — finite exact rational Cramer/adjugate absorption candidate

The proposed reference algorithm is a total pure rational function on any
finite matrix; its matrix inverse is expressed through explicit rational
adjugate/determinant arithmetic, not a noncomputable choice. Verification
of the resulting equations by `checkDirichlet` is exact. A future generic
Dirichlet nonsingularity theorem must prove the checker accepts the
reference candidate for EVERY valid Markov matrix; mere total evaluation
of rational division (including zero determinants) is not that theorem.
-/
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- Input-dependent recurrent union from the computable bottom classes. -/
def rationalRecurrentUnion {n : ℕ} (K : RationalMarkovMatrix n) :
    Finset (Fin n) :=
  (bottomClasses K).biUnion (fun C => C)

/-- Full-state transient-restricted Q, avoiding the generally singular
`I-K` for the entire row-stochastic matrix. Recurrent rows/columns of Q
are zero. -/
def killedTransientEntry {n : ℕ} (K : RationalMarkovMatrix n)
    (x y : Fin n) : ℚ :=
  if x ∈ rationalRecurrentUnion K then 0
  else if y ∈ rationalRecurrentUnion K then 0
  else K.entry x y

/-- Dirichlet matrix A = I - Q. When every state is recurrent A = I. -/
def dirichletMatrix {n : ℕ} (K : RationalMarkovMatrix n) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun x y => (if x = y then 1 else 0) - killedTransientEntry K x y

/-- Boundary forcing for entry into the selected bottom class. -/
def dirichletRHS {n : ℕ} (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (x : Fin n) : ℚ :=
  if x ∈ rationalRecurrentUnion K then
    (if x ∈ C then 1 else 0)
  else ∑ z ∈ C, K.entry x z

/-- Exact Cramer/adjugate formula. The following computation is finite
and uses only rational arithmetic; a zero determinant is NOT a valid
absorption certificate and must be rejected by the exact checker. -/
def cramerWeight {n : ℕ}
    (K : RationalMarkovMatrix n) (C : Finset (Fin n)) (x : Fin n) : ℚ :=
  (∑ y : Fin n,
    (dirichletMatrix K).adjugate x y * dirichletRHS K C y) /
    (dirichletMatrix K).det

/-- The first algorithmic certificate candidate. -/
def referenceDirichletCertificate {n : ℕ}
    (K : RationalMarkovMatrix n) : DirichletCertificate n where
  classes := bottomClasses K
  weight := fun C x => cramerWeight K C x

/-- A useful executable Boolean: this checks, rather than assumes,
complete exact rational conditions for a generated candidate. -/
def verifyReferenceDirichlet {n : ℕ}
    (K : RationalMarkovMatrix n) : Bool :=
  checkDirichlet K (referenceDirichletCertificate K)

/-- Accepted output is an algebraic certificate, with no custom axiom. -/
theorem verifiedReference_sound {n : ℕ}
    (K : RationalMarkovMatrix n)
    (h : verifyReferenceDirichlet K = true) :
    DirichletConditions K (referenceDirichletCertificate K) :=
  checkDirichlet_sound K (referenceDirichletCertificate K) h

end C10
end ReverseSolver
end PermanssonResearch