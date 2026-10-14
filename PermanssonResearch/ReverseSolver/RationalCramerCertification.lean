import PermanssonResearch.ReverseSolver.RationalCramerBounds
import PermanssonResearch.ReverseSolver.RationalCramerPartition
import PermanssonResearch.ReverseSolver.FiniteAbsorptionDirichlet
import Mathlib.Tactic

/-!
# C10 — unconditional acceptance of the total rational Cramer reference solver

Every nonempty finite stochastic rational matrix has a nonsingular
Dirichlet matrix. Its exact Cramer table satisfies all class boundaries,
full stochastic harmonic equations, unit-interval bounds and total class
mass one. Therefore the executable reference certificate passes the
complete independently defined exact checker on *every* valid input.
This is an algebraic/proof-carrying computation theorem, not yet the
additional identification with a genuine canonical infinite-path law.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- The exact finite Boolean checker accepts every table that really
satisfies the full Dirichlet contract. -/
theorem checkDirichlet_complete {n : ℕ}
    (K : RationalMarkovMatrix n) (cert : DirichletCertificate n)
    (h : DirichletConditions K cert) :
    checkDirichlet K cert = true := by
  unfold checkDirichlet
  apply (andB_eq_true_iff _ _).mpr
  constructor
  · apply (andB_eq_true_iff _ _).mpr
    constructor
    · simpa only [decide_eq_true_eq] using h.1
    · have hRows : ∀ i : Fin n, ComponentConditions K cert i := by
        intro i
        change component K i ∈ cert.classes → _
        intro hMember
        exact ⟨h.2.1 (component K i) hMember,
          h.2.2.1 (component K i) hMember⟩
      simpa only [decide_eq_true_eq] using hRows
  · simpa only [decide_eq_true_eq] using h.2.2.2

/-- Generic exact Cramer candidate satisfies the COMPLETE algebraic
certificate contract for each valid nonempty rational Markov matrix. -/
theorem referenceDirichlet_conditions {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) :
    DirichletConditions K (referenceDirichletCertificate K) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro C hC x
    change if x ∈ rationalRecurrentUnion K then
        cramerWeight K C x = (if x ∈ C then 1 else 0)
      else cramerWeight K C x =
        ∑ y : Fin n, K.entry x y * cramerWeight K C y
    by_cases hx : x ∈ rationalRecurrentUnion K
    · simpa [hx] using cramerWeight_boundary K C x hx
    · simpa [hx] using cramerWeight_transient_harmonic K C hC x hx
  · intro C hC x
    change 0 ≤ cramerWeight K C x ∧ cramerWeight K C x ≤ 1
    exact cramerWeight_unit_interval K C hC x
  · intro x
    change cramerTotal K x = 1
    exact cramerTotal_eq_one K x

/-- Total Cramer evaluation is not merely a candidate: every produced
exact rational certificate passes the entire independent checker. -/
theorem referenceDirichlet_check_true {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n) :
    verifyReferenceDirichlet K = true := by
  unfold verifyReferenceDirichlet
  exact checkDirichlet_complete K (referenceDirichletCertificate K)
    (referenceDirichlet_conditions K)

end C10
end ReverseSolver
end PermanssonResearch