import PermanssonResearch.ReverseSolver.FrozenMenu
import Mathlib.Tactic

/-!
# D0-B: exact finite rational stochastic matrices

Rows are indexed by the finite joint state space. The entries are rationals,
never floating-point approximations, and every row is certified stochastic.
This standalone finite representation is *not* automatically an induced
strategic-world kernel: a separate correspondence is required.
-/

namespace PermanssonResearch
namespace ReverseSolver

/-- Exact rational transition data, with certified Markov row normalization. -/
structure RationalMarkovMatrix (n : ℕ) where
  entry : Fin n → Fin n → ℚ
  entry_nonneg : ∀ y z, 0 ≤ entry y z
  row_sum_one : ∀ y, (∑ z : Fin n, entry y z) = 1

/-- A disjoint finite target/forbidden query. -/
structure RationalHittingTarget (n : ℕ) where
  goal : Finset (Fin n)
  forbidden : Finset (Fin n)
  disjoint : Disjoint goal forbidden

/-- Finite horizon, in *transitions*, with time zero counted. The recursion
holds the same matrix fixed for the full horizon; G and D are terminal only
for evaluation, not actual absorbing states of the matrix. -/
def rationalHittingValue {n : ℕ} (K : RationalMarkovMatrix n)
    (target : RationalHittingTarget n) : ℕ → Fin n → ℚ
  | 0, y => if y ∈ target.goal then 1 else 0
  | t + 1, y =>
      if y ∈ target.goal then 1
      else if y ∈ target.forbidden then 0
      else ∑ z : Fin n, K.entry y z * rationalHittingValue K target t z

@[simp] theorem rationalHittingValue_zero {n : ℕ}
    (K : RationalMarkovMatrix n) (target : RationalHittingTarget n)
    (y : Fin n) :
    rationalHittingValue K target 0 y =
      if y ∈ target.goal then 1 else 0 := rfl

theorem rationalHittingValue_succ {n : ℕ}
    (K : RationalMarkovMatrix n) (target : RationalHittingTarget n)
    (t : ℕ) (y : Fin n) :
    rationalHittingValue K target (t+1) y =
      if y ∈ target.goal then 1 else
      if y ∈ target.forbidden then 0 else
        ∑ z : Fin n, K.entry y z * rationalHittingValue K target t z := rfl

/-- Exact probability bounds for every finite horizon, including the
zero-step boundary and nonabsorbing underlying transition matrices. -/
theorem rationalHittingValue_mem_Icc {n : ℕ}
    (K : RationalMarkovMatrix n) (target : RationalHittingTarget n) :
    ∀ (t : ℕ) (y : Fin n),
      0 ≤ rationalHittingValue K target t y ∧
        rationalHittingValue K target t y ≤ 1 := by
  intro t
  induction t with
  | zero =>
      intro y
      simp [rationalHittingValue]
      split_ifs <;> norm_num
  | succ t ih =>
      intro y
      rw [rationalHittingValue_succ]
      split_ifs
      · exact ⟨by norm_num, le_refl _⟩
      · exact ⟨le_refl _, by norm_num⟩
      · constructor
        · exact Finset.sum_nonneg fun z _ =>
            mul_nonneg (K.entry_nonneg y z) (ih z).1
        · calc
            (∑ z : Fin n, K.entry y z * rationalHittingValue K target t z) ≤
                ∑ z : Fin n, K.entry y z * 1 := by
                  apply Finset.sum_le_sum
                  intro z hz
                  exact mul_le_mul_of_nonneg_left (ih z).2 (K.entry_nonneg y z)
            _ = 1 := by simpa using K.row_sum_one y

end ReverseSolver
end PermanssonResearch
