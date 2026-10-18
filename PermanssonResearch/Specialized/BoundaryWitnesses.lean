import PermanssonResearch.Specialized.FiniteDetection
import PermanssonResearch.Specialized.ShellSchur

/-! Concrete failures of the missing legal, embedding, shell dimension and
strict-shift premises. These are proved negative statements, not compiler mutants. -/

namespace PermanssonResearch.Specialized.BoundaryWitnesses

open Matrix

def negativeForm (x : ℝ) : ℝ := -(x * x)
def changedForm (x : ℝ) : ℝ := x * x

theorem changed_embedding_loses_negativity :
    negativeForm 1 < 0 ∧ ¬ changedForm 1 < 0 ∧
      ¬ (∀ x : ℝ, changedForm (id x) = negativeForm x) := by
  refine ⟨by norm_num [negativeForm], by norm_num [changedForm], ?_⟩
  intro h
  have := h 1
  norm_num [changedForm, negativeForm] at this

theorem exact_but_illegal_approximant :
    ‖(1 : ℝ) - 1‖ = 0 ∧ negativeForm 1 < 0 ∧
      (1 : ℝ) ∉ ({0} : Set ℝ) ∧
      ¬ ∃ p ∈ ({0} : Set ℝ), negativeForm p < 0 := by
  norm_num [negativeForm]

noncomputable def shell : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, 0]

/-- The first scalar shell equation holds, but the full two-dimensional shell
equation fails on the same vector. The core shift is strictly negative. -/
theorem dimension_two_retains_second_equation :
    let S := shellComplement (0 : Matrix (Fin 1) (Fin 1) ℝ)
      (0 : Matrix (Fin 1) (Fin 2) ℝ) shell (-1)
    S 0 0 = 0 ∧ (S *ᵥ ![0, 1]) 0 = 0 ∧ (S *ᵥ ![0, 1]) 1 = 1 ∧
      S *ᵥ ![0, 1] ≠ 0 := by
  change (shellComplement (0 : Matrix (Fin 1) (Fin 1) ℝ)
    (0 : Matrix (Fin 1) (Fin 2) ℝ) shell (-1)) 0 0 = 0 ∧ _
  simp only [shellComplement, Matrix.transpose_zero, zero_mul, sub_zero]
  norm_num [negativeShift, shell, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.one_apply]
  intro h
  have hh := congrArg (fun v : Fin 2 → ℝ => v 1) h
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] at hh

theorem zero_shift_does_not_supply_inverse :
    ¬ IsUnit (negativeShift (0 : Matrix (Fin 1) (Fin 1) ℝ) 0) := by
  simp [negativeShift]

end PermanssonResearch.Specialized.BoundaryWitnesses
