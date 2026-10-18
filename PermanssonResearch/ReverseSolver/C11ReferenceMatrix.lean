import PermanssonResearch.MultipleLimit.FiniteInvariantExistence
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# A nonsingular rational stationary matrix for every finite irreducible chain

The matrix is exactly `I - Pᵀ + 11ᵀ`. Its transpose kernel is zero by a
stochastic maximum/minimum argument and positive-edge irreducibility.
-/

namespace PermanssonResearch.ReverseSolver.C11

open Matrix

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]

def referenceMatrix (P : Matrix Y Y ℚ) : Matrix Y Y ℚ :=
  fun i j => (if i=j then 1 else 0)-P j i+1

private theorem referenceMatrix_transpose_row (P : Matrix Y Y ℚ) (u : Y → ℚ) (x : Y) :
    (referenceMatrix P).transpose.mulVec u x =
      u x-(∑ y : Y, P x y*u y)+(∑ y : Y, u y) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, referenceMatrix]
  simp_rw [add_mul, sub_mul]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [eq_comm]

private theorem harmonic_maximum_propagates (P : Matrix Y Y ℚ)
    (hP : ∀ x y, 0≤P x y) (hrow : ∀ x, ∑ y : Y, P x y=1)
    (u : Y → ℚ) (hhar : ∀ x, u x=∑ y : Y, P x y*u y)
    (x : Y) (hmax : ∀ y, u y≤u x) (y : Y)
    (hpath : Relation.ReflTransGen (fun a b => 0<P a b) x y) : u y=u x := by
  induction hpath with
  | refl => rfl
  | @tail a b hab hedge ih =>
      have hsum : (∑ z : Y, P a z*(u x-u z))=0 := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, one_mul, ← hhar, ih]
        ring
      have hnonneg : ∀ z : Y, 0≤P a z*(u x-u z) :=
        fun z => mul_nonneg (hP a z) (sub_nonneg.mpr (hmax z))
      have hle : P a b*(u x-u b)≤0 := by
        simpa only [hsum] using Finset.single_le_sum
          (s := (Finset.univ : Finset Y)) (fun z _ => hnonneg z) (Finset.mem_univ b)
      have hgap : u x-u b≤0 := nonpos_of_mul_nonpos_right hle hedge
      linarith [hmax b]

theorem referenceMatrix_transpose_kernel_zero (P : Matrix Y Y ℚ)
    (hP : ∀ x y, 0≤P x y) (hrow : ∀ x, ∑ y : Y, P x y=1)
    (hirr : ∀ x y, Relation.ReflTransGen (fun a b => 0<P a b) x y)
    (u : Y → ℚ) (hu : (referenceMatrix P).transpose.mulVec u=0) : u=0 := by
  obtain ⟨xmax,hmax⟩ := Finite.exists_max u
  obtain ⟨xmin,hmin⟩ := Finite.exists_min u
  have hupper : (∑ y : Y, P xmax y*u y)≤u xmax := by
    calc
      _ ≤ ∑ y : Y, P xmax y*u xmax := Finset.sum_le_sum
        (fun y _ => mul_le_mul_of_nonneg_left (hmax y) (hP xmax y))
      _ = u xmax := by rw [← Finset.sum_mul, hrow, one_mul]
  have hlower : u xmin≤∑ y : Y, P xmin y*u y := by
    calc
      u xmin = ∑ y : Y, P xmin y*u xmin := by rw [← Finset.sum_mul, hrow, one_mul]
      _ ≤ _ := Finset.sum_le_sum
        (fun y _ => mul_le_mul_of_nonneg_left (hmin y) (hP xmin y))
  have he (x : Y) : u x-(∑ y : Y, P x y*u y)+(∑ y : Y, u y)=0 := by
    simpa only [referenceMatrix_transpose_row, Pi.zero_apply] using congrFun hu x
  have hsum : (∑ y : Y, u y)=0 := by linarith [he xmax,he xmin]
  have hhar : ∀ x, u x=∑ y : Y, P x y*u y := by intro x; linarith [he x]
  have hconstant : ∀ y, u y=u xmax :=
    fun y => harmonic_maximum_propagates P hP hrow u hhar xmax hmax y (hirr xmax y)
  have hxzero : u xmax=0 := by
    have hc : (Fintype.card Y : ℚ)≠0 := by exact_mod_cast Fintype.card_ne_zero
    simp_rw [hconstant] at hsum
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    exact (mul_eq_zero.mp hsum).resolve_left hc
  funext y
  simpa only [Pi.zero_apply, hxzero] using hconstant y

theorem referenceMatrix_det_ne_zero (P : Matrix Y Y ℚ)
    (hP : ∀ x y, 0≤P x y) (hrow : ∀ x, ∑ y : Y, P x y=1)
    (hirr : ∀ x y, Relation.ReflTransGen (fun a b => 0<P a b) x y) :
    (referenceMatrix P).det≠0 := by
  intro hd
  have ht : (referenceMatrix P).transpose.det=0 := by rwa [Matrix.det_transpose]
  obtain ⟨u,hunonzero,hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ht
  exact hunonzero (referenceMatrix_transpose_kernel_zero P hP hrow hirr u hu)

/-- Exact rational column-replacement determinant formula. -/
def referenceWeights (P : Matrix Y Y ℚ) (x : Y) : ℚ :=
  Matrix.cramer (referenceMatrix P) (fun _ => 1) x/(referenceMatrix P).det

theorem referenceWeights_matrix_equation (P : Matrix Y Y ℚ)
    (hd : (referenceMatrix P).det≠0) (x : Y) :
    (∑ y : Y, referenceMatrix P x y*referenceWeights P y)=1 := by
  have hm := congrFun (Matrix.mulVec_cramer (referenceMatrix P) (fun _ => (1:ℚ))) x
  have he : (∑ y : Y, referenceMatrix P x y*
      Matrix.cramer (referenceMatrix P) (fun _ => 1) y)=(referenceMatrix P).det := by
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_one] using hm
  simp only [referenceWeights, ← mul_div_assoc, ← Finset.sum_div, he, div_self hd]

end PermanssonResearch.ReverseSolver.C11
