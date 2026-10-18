import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-! E-SHELL: the actual finite shell is retained as an arbitrary finite index
type. Only a one-dimensional shell has a scalar equation. Source carriers and
their model interpretation remain explicit external mathematical obligations. -/

open Matrix

namespace PermanssonResearch.Specialized

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def negativeShift (H : Matrix ι ι ℝ) (ell : ℝ) : Matrix ι ι ℝ := H - ell • 1

theorem negativeShift_posDef (H : Matrix ι ι ℝ) (hH : H.PosSemidef)
    {ell : ℝ} (hell : ell < 0) : (negativeShift H ell).PosDef := by
  have hp : ((-ell) • (1 : Matrix ι ι ℝ)).PosDef :=
    Matrix.PosDef.one.smul (neg_pos.mpr hell)
  simpa [negativeShift, sub_eq_add_neg, neg_smul] using Matrix.PosDef.posSemidef_add hH hp

theorem negativeShift_isUnit (H : Matrix ι ι ℝ) (hH : H.PosSemidef)
    {ell : ℝ} (hell : ell < 0) : IsUnit (negativeShift H ell) :=
  (negativeShift_posDef H hH hell).isUnit

noncomputable def shellComplement (H : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ κ ℝ) (ell : ℝ) : Matrix κ κ ℝ :=
  negativeShift C ell - B.transpose * (negativeShift H ell)⁻¹ * B

/-- Gaussian block elimination applies for every finite shell dimension. -/
theorem shell_determinant (H : Matrix ι ι ℝ) (hH : H.PosSemidef)
    (B : Matrix ι κ ℝ) (C : Matrix κ κ ℝ) {ell : ℝ} (hell : ell < 0) :
    (Matrix.fromBlocks (negativeShift H ell) B B.transpose (negativeShift C ell)).det =
      (negativeShift H ell).det * (shellComplement H B C ell).det := by
  letI := (negativeShift_isUnit H hH hell).invertible
  simpa [shellComplement, Matrix.invOf_eq_nonsing_inv] using
    Matrix.det_fromBlocks₁₁ (negativeShift H ell) B B.transpose (negativeShift C ell)

/-- Both directions of the eigen-equation elimination, with an actual matrix
inverse whose existence has been proved from PSD and a negative shift. -/
theorem shell_equations_iff (H : Matrix ι ι ℝ) (hH : H.PosSemidef)
    (B : Matrix ι κ ℝ) (C : Matrix κ κ ℝ) {ell : ℝ} (hell : ell < 0)
    (v : ι → ℝ) (w : κ → ℝ) :
    ((negativeShift H ell) *ᵥ v + B *ᵥ w = 0 ∧
      B.transpose *ᵥ v + (negativeShift C ell) *ᵥ w = 0) ↔
    (v = -((negativeShift H ell)⁻¹ *ᵥ (B *ᵥ w)) ∧
      (shellComplement H B C ell) *ᵥ w = 0) := by
  letI := (negativeShift_isUnit H hH hell).invertible
  have hcancel : ∀ z : ι → ℝ,
      (negativeShift H ell)⁻¹ *ᵥ ((negativeShift H ell) *ᵥ z) = z := by
    intro z
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  constructor
  · rintro ⟨hfirst, hsecond⟩
    have hv : v = -((negativeShift H ell)⁻¹ *ᵥ (B *ᵥ w)) := by
      have he : (negativeShift H ell) *ᵥ v = -(B *ᵥ w) := eq_neg_of_add_eq_zero_left hfirst
      have hi := congrArg (fun z => (negativeShift H ell)⁻¹ *ᵥ z) he
      simpa [hcancel, Matrix.mulVec_neg] using hi
    refine ⟨hv, ?_⟩
    rw [hv, Matrix.mulVec_neg] at hsecond
    rw [shellComplement, Matrix.sub_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simpa only [sub_eq_add_neg, add_comm] using hsecond
  · rintro ⟨hv, hsecond⟩
    constructor
    · rw [hv, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
        Matrix.mul_inv_of_invertible, Matrix.one_mulVec, neg_add_cancel]
    · rw [hv, Matrix.mulVec_neg]
      rw [shellComplement, Matrix.sub_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hsecond
      simpa only [sub_eq_add_neg, add_comm] using hsecond

theorem negative_eigenvector_has_nonzero_shell
    (H : Matrix ι ι ℝ) (hH : H.PosSemidef)
    (B : Matrix ι κ ℝ) (C : Matrix κ κ ℝ) {ell : ℝ} (hell : ell < 0)
    (v : ι → ℝ) (w : κ → ℝ)
    (heq : (negativeShift H ell) *ᵥ v + B *ᵥ w = 0 ∧
      B.transpose *ᵥ v + (negativeShift C ell) *ᵥ w = 0)
    (hne : v ≠ 0 ∨ w ≠ 0) : w ≠ 0 := by
  intro hw
  have hv := ((shell_equations_iff H hH B C hell v w).mp heq).1
  have hv0 : v = 0 := by simpa [hw] using hv
  exact hne.elim (fun h => h hv0) (fun h => h hw)

/-- Well-ordering provides the first bad carrier only after a bad carrier has
been established. This does not assert that a negative carrier exists. -/
theorem exists_first_bad (bad : ℕ → Prop) (hex : ∃ n, bad n) :
    ∃ n, bad n ∧ ∀ m < n, ¬ bad m := by
  classical
  exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩

end PermanssonResearch.Specialized
