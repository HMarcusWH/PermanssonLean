import Mathlib.Tactic

/-!
# ApplicationBridge: exact rational LP certificates

This module proves *certificate checking soundness*, not completeness of an
LP solver. The application first transforms a bounded finite rational LP into
`x ≥ 0, A x ≤ b` with objective `max c · x`; the translation, source identity,
and original-variable offset must be authenticated separately. A primal/dual
pair with matching objective is optimal even for real-valued competitors.
A Farkas multiplier with a negative right side witnesses infeasibility.

No observation data, empirical identification, general nonlinear optimization,
solver-choice uniqueness, release status or independent CERT is asserted.
-/

namespace PermanssonResearch.ApplicationBridge.LinearProgramReceipt

set_option autoImplicit false

variable {m n : ℕ}

/-- All variables are nonnegative, with the *complete* constraint matrix. -/
def primalFeasible (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ (∀ i, (∑ j : Fin n, A i j * x j) ≤ b i)

/-- Dual constraints for `max c·x` subject to `A x ≤ b, x ≥ 0`. -/
def dualFeasible (A : Fin m → Fin n → ℚ) (c : Fin n → ℚ)
    (y : Fin m → ℚ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ j, c j ≤ ∑ i : Fin m, y i * A i j)

def objective (c : Fin n → ℚ) (x : Fin n → ℚ) : ℚ :=
  ∑ j : Fin n, c j * x j

def dualBound (b : Fin m → ℚ) (y : Fin m → ℚ) : ℚ :=
  ∑ i : Fin m, y i * b i

/-- Pure finite distributivity; the same identity works over rational and real
    coefficients, so the certificate theorem can be lifted to real competitors. -/
private theorem swap_weighted {R : Type*} [CommSemiring R]
    (A : Fin m → Fin n → R) (y : Fin m → R) (x : Fin n → R) :
    (∑ j : Fin n, (∑ i : Fin m, y i * A i j) * x j) =
      ∑ i : Fin m, y i * (∑ j : Fin n, A i j * x j) := by
  classical
  calc
    _ = ∑ j : Fin n, ∑ i : Fin m, (y i * A i j) * x j := by
      simp only [Finset.sum_mul]
    _ = ∑ i : Fin m, ∑ j : Fin n, (y i * A i j) * x j := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin m, y i * (∑ j : Fin n, A i j * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Checked rational primal and dual feasibility imply weak duality. -/
theorem weak_duality (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (c : Fin n → ℚ) (x : Fin n → ℚ) (y : Fin m → ℚ)
    (hx : primalFeasible A b x) (hy : dualFeasible A c y) :
    objective c x ≤ dualBound b y := by
  classical
  rcases hx with ⟨hx0, hxrow⟩
  rcases hy with ⟨hy0, hycol⟩
  calc
    objective c x ≤ ∑ j : Fin n, (∑ i : Fin m, y i * A i j) * x j := by
      unfold objective
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hycol j) (hx0 j))
    _ = ∑ i : Fin m, y i * (∑ j : Fin n, A i j * x j) :=
      swap_weighted A y x
    _ ≤ dualBound b y := by
      unfold dualBound
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hxrow i) (hy0 i))

/-- Exact zero primal-dual gap is a global optimum over all rational feasible
    vectors, even if multiple optima exist or the candidate solver chose one. -/
theorem optimum_of_matching_certificate (A : Fin m → Fin n → ℚ)
    (b : Fin m → ℚ) (c : Fin n → ℚ)
    (x : Fin n → ℚ) (y : Fin m → ℚ)
    (hx : primalFeasible A b x) (hy : dualFeasible A c y)
    (hmatch : objective c x = dualBound b y) :
    ∀ z : Fin n → ℚ, primalFeasible A b z → objective c z ≤ objective c x := by
  intro z hz
  exact (weak_duality A b c z y hz hy).trans_eq hmatch.symm

/-- Exact checked certificate is optimal over *real* feasible competitors;
    all coefficients remain the original rational source coefficients. -/
theorem optimum_over_reals (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (c : Fin n → ℚ) (x : Fin n → ℚ) (y : Fin m → ℚ)
    (_hx : primalFeasible A b x) (hy : dualFeasible A c y)
    (hmatch : objective c x = dualBound b y) :
    ∀ z : Fin n → ℝ,
      (∀ j, 0 ≤ z j) →
      (∀ i, (∑ j : Fin n, (A i j : ℝ) * z j) ≤ (b i : ℝ)) →
      (∑ j : Fin n, (c j : ℝ) * z j) ≤
        ∑ j : Fin n, (c j : ℝ) * (x j : ℝ) := by
  classical
  intro z hz0 hzrow
  have hy0 : ∀ i, (0 : ℝ) ≤ (y i : ℝ) := by
    intro i
    exact_mod_cast hy.1 i
  have hycol : ∀ j, (c j : ℝ) ≤ ∑ i : Fin m, (y i : ℝ) * (A i j : ℝ) := by
    intro j
    exact_mod_cast hy.2 j
  have hgap : (∑ i : Fin m, (y i : ℝ) * (b i : ℝ)) =
      ∑ j : Fin n, (c j : ℝ) * (x j : ℝ) := by
    have eq : dualBound b y = objective c x := hmatch.symm
    unfold dualBound objective at eq
    exact_mod_cast eq
  calc
    (∑ j : Fin n, (c j : ℝ) * z j) ≤
        ∑ j : Fin n, (∑ i : Fin m, (y i : ℝ) * (A i j : ℝ)) * z j := by
          exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hycol j) (hz0 j))
    _ = ∑ i : Fin m, (y i : ℝ) * (∑ j : Fin n, (A i j : ℝ) * z j) :=
      swap_weighted (fun i j => (A i j : ℝ)) (fun i => (y i : ℝ)) z
    _ ≤ ∑ i : Fin m, (y i : ℝ) * (b i : ℝ) := by
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hzrow i) (hy0 i))
    _ = ∑ j : Fin n, (c j : ℝ) * (x j : ℝ) := hgap

/-- A strict Farkas separator rules out *every* nonnegative rational primal
    vector. No candidate-search timeout can be substituted for this witness. -/
theorem infeasible_of_farkas (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (y : Fin m → ℚ)
    (hy0 : ∀ i, 0 ≤ y i)
    (hycol : ∀ j, 0 ≤ ∑ i : Fin m, y i * A i j)
    (hybound : (∑ i : Fin m, y i * b i) < 0) :
    ¬ ∃ x : Fin n → ℚ, primalFeasible A b x := by
  classical
  rintro ⟨x, hx⟩
  have hnonneg : (0 : ℚ) ≤ ∑ j : Fin n, (∑ i : Fin m, y i * A i j) * x j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hycol j) (hx.1 j))
  have hrow : (∑ j : Fin n, (∑ i : Fin m, y i * A i j) * x j) ≤
      ∑ i : Fin m, y i * b i := by
    rw [swap_weighted A y x]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx.2 i) (hy0 i))
  exact (not_lt_of_ge (hnonneg.trans hrow)) hybound

/-- A verified Farkas multiplier also excludes every real feasible vector;
    the rational/real coercion is justified by the exact checked inequalities. -/
theorem infeasible_over_reals (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (y : Fin m → ℚ)
    (hy0 : ∀ i, 0 ≤ y i)
    (hycol : ∀ j, 0 ≤ ∑ i : Fin m, y i * A i j)
    (hybound : (∑ i : Fin m, y i * b i) < 0) :
    ¬ ∃ z : Fin n → ℝ,
        (∀ j, 0 ≤ z j) ∧
        (∀ i, (∑ j : Fin n, (A i j : ℝ) * z j) ≤ (b i : ℝ)) := by
  classical
  rintro ⟨z, hz0, hzrow⟩
  have hyreal : ∀ i, (0 : ℝ) ≤ (y i : ℝ) := by
    intro i
    exact_mod_cast hy0 i
  have hcolreal : ∀ j, (0 : ℝ) ≤ ∑ i : Fin m, (y i : ℝ) * (A i j : ℝ) := by
    intro j
    exact_mod_cast hycol j
  have hb : (∑ i : Fin m, (y i : ℝ) * (b i : ℝ)) < 0 := by
    exact_mod_cast hybound
  have hnonneg : (0 : ℝ) ≤
      ∑ j : Fin n, (∑ i : Fin m, (y i : ℝ) * (A i j : ℝ)) * z j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hcolreal j) (hz0 j))
  have hrow : (∑ j : Fin n, (∑ i : Fin m, (y i : ℝ) * (A i j : ℝ)) * z j) ≤
      ∑ i : Fin m, (y i : ℝ) * (b i : ℝ) := by
    rw [swap_weighted (fun i j => (A i j : ℝ)) (fun i => (y i : ℝ)) z]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hzrow i) (hyreal i))
  exact (not_lt_of_ge (hnonneg.trans hrow)) hb

end PermanssonResearch.ApplicationBridge.LinearProgramReceipt
