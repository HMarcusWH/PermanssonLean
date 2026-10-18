import PermanssonResearch.ReverseSolver.PolytopeActive
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Rational active-set reference candidates

A selected active family may contain dependent rows. Its Gram determinant tests
full column rank directly, so no dependent-equality elimination is assumed.
-/

namespace PermanssonResearch.ReverseSolver.ExactPolytope

open Matrix Set

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def selectedRows {R : Type*} [Zero R] (A : Matrix I J R) (s : Finset I) : Matrix I J R :=
  fun i j => if i ∈ s then A i j else 0

def selectedGram {R : Type*} [CommRing R] (A : Matrix I J R) (s : Finset I) : Matrix J J R :=
  (selectedRows A s).transpose * selectedRows A s

theorem selectedGram_kernel_iff (A : Matrix I J ℝ) (s : Finset I) (z : J → ℝ) :
    (selectedGram A s).mulVec z = 0 ↔ (selectedRows A s).mulVec z = 0 := by
  constructor
  · intro h
    have he := congrArg (fun v => dotProduct z v) h
    rw [selectedGram, ← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
      dotProduct_zero] at he
    exact dotProduct_self_eq_zero.mp he
  · intro h
    rw [selectedGram, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

theorem extreme_active_gram_det_ne_zero (A : Matrix I J ℝ) (b : I → ℝ)
    (x : J → ℝ) (hx : x ∈ (feasible A b).extremePoints ℝ) :
    (selectedGram A (Finset.univ.filter fun i => dotProduct (A i) x = b i)).det ≠ 0 := by
  classical
  intro hd
  obtain ⟨z, hn, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  apply hn
  apply extreme_active_kernel_zero A b x hx z
  intro i hi
  have hh := congrFun ((selectedGram_kernel_iff A _ z).mp hz) i
  have himem : i ∈ Finset.univ.filter (fun i => dotProduct (A i) x = b i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  simpa only [Matrix.mulVec, selectedRows, if_pos himem, Pi.zero_apply] using hh

def gramRhs (A : Matrix I J ℚ) (b : I → ℚ) (s : Finset I) : J → ℚ :=
  (selectedRows A s).transpose.mulVec (fun i => if i ∈ s then b i else 0)

/-- Total rational output. A zero determinant is discarded by the candidate filter. -/
def rationalCandidate (A : Matrix I J ℚ) (b : I → ℚ) (s : Finset I) : J → ℚ :=
  fun j => Matrix.cramer (selectedGram A s) (gramRhs A b s) j / (selectedGram A s).det

theorem rationalCandidate_equation (A : Matrix I J ℚ) (b : I → ℚ)
    (s : Finset I) (hd : (selectedGram A s).det ≠ 0) :
    (selectedGram A s).mulVec (rationalCandidate A b s) = gramRhs A b s := by
  have he : rationalCandidate A b s = (selectedGram A s).det⁻¹ •
      Matrix.cramer (selectedGram A s) (gramRhs A b s) := by
    funext j
    simp [rationalCandidate, div_eq_mul_inv, mul_comm]
  rw [he, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul,
    inv_mul_cancel₀ hd, one_smul]

def rationalFeasible (A : Matrix I J ℚ) (b : I → ℚ) (x : J → ℚ) : Prop :=
  ∀ i, dotProduct (A i) x ≤ b i

instance rationalFeasibleDecidable (A : Matrix I J ℚ) (b : I → ℚ) (x : J → ℚ) :
    Decidable (rationalFeasible A b x) := inferInstanceAs (Decidable (∀ i, _))

/-- Finite exhaustive exact candidates; feasibility is checked in rational arithmetic. -/
def rationalCandidates (A : Matrix I J ℚ) (b : I → ℚ) : Finset (J → ℚ) :=
  (((Finset.univ : Finset (Finset I)).filter fun s => (selectedGram A s).det ≠ 0).image
    (rationalCandidate A b)).filter (rationalFeasible A b)

theorem rationalCandidates_feasible (A : Matrix I J ℚ) (b : I → ℚ)
    (x : J → ℚ) (hx : x ∈ rationalCandidates A b) : rationalFeasible A b x :=
  (Finset.mem_filter.mp hx).2

end PermanssonResearch.ReverseSolver.ExactPolytope
