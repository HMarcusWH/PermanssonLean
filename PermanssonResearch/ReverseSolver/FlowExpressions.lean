import PermanssonResearch.ReverseSolver.PolytopeLinearProgram

namespace PermanssonResearch.ReverseSolver.ExactPolytope

open Matrix

variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K]

def evaluate (e : J → ℚ) (x : J → ℝ) : ℝ := ∑ j, (e j : ℝ) * x j

def coordinate (j : J) : J → ℚ := Pi.single j 1

@[simp] theorem evaluate_coordinate (j : J) (x : J → ℝ) :
    evaluate (coordinate j) x = x j := by
  classical
  simp [evaluate, coordinate, Pi.single_apply, apply_ite, ite_mul]

@[simp] theorem evaluate_zero (x : J → ℝ) : evaluate 0 x = 0 := by simp [evaluate]

@[simp] theorem evaluate_add (e f : J → ℚ) (x : J → ℝ) :
    evaluate (e + f) x = evaluate e x + evaluate f x := by
  simp [evaluate, add_mul, Finset.sum_add_distrib]

@[simp] theorem evaluate_sub (e f : J → ℚ) (x : J → ℝ) :
    evaluate (e - f) x = evaluate e x - evaluate f x := by
  simp [evaluate, sub_mul, Finset.sum_sub_distrib]

@[simp] theorem evaluate_neg (e : J → ℚ) (x : J → ℝ) :
    evaluate (-e) x = -evaluate e x := by simp [evaluate]

@[simp] theorem evaluate_smul (a : ℚ) (e : J → ℚ) (x : J → ℝ) :
    evaluate (a • e) x = (a : ℝ) * evaluate e x := by
  simp [evaluate, mul_assoc, Finset.mul_sum]

@[simp] theorem evaluate_sum (e : K → J → ℚ) (x : J → ℝ) :
    evaluate (∑ k, e k) x = ∑ k, evaluate (e k) x := by
  simp only [evaluate, Finset.sum_apply, Rat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

def equalityConstraints (e : J → ℚ) (b : ℚ) : List (RationalConstraint J) :=
  [⟨e,b⟩,⟨-e,-b⟩]

theorem constraint_holds (a : RationalConstraint J) (x : J → ℝ) :
    a.holds x ↔ evaluate a.coefficient x ≤ (a.bound : ℝ) := Iff.rfl

theorem equalityConstraints_iff (e : J → ℚ) (b : ℚ) (x : J → ℝ) :
    (∀ a ∈ equalityConstraints e b, a.holds x) ↔ evaluate e x = (b : ℝ) := by
  constructor
  · intro h
    have hle : evaluate e x ≤ (b : ℝ) := h ⟨e,b⟩ (by simp [equalityConstraints])
    have hneg := h ⟨-e,-b⟩ (by simp [equalityConstraints])
    have hge : (b : ℝ) ≤ evaluate e x := by
      simpa only [constraint_holds, evaluate_neg, Rat.cast_neg, neg_le_neg_iff] using hneg
    exact le_antisymm hle hge
  · intro h a ha
    have he : a = ⟨e,b⟩ ∨ a = ⟨-e,-b⟩ := by simpa [equalityConstraints] using ha
    rcases he with rfl | rfl
    · change evaluate e x ≤ (b : ℝ)
      exact h.le
    · rw [constraint_holds]
      simpa only [evaluate_neg, h, Rat.cast_neg] using (le_refl (-(b : ℝ)))

end PermanssonResearch.ReverseSolver.ExactPolytope
