import PermanssonResearch.ReverseSolver.BeliefKernel

/-! Finite observation-policy trees and the alpha-vector Bellman theorem.
A continuation is selected separately for each observed branch. Neither tree
nodes nor their controller choices receive the hidden augmented state. -/

namespace PermanssonResearch.ReverseSolver.Belief

set_option autoImplicit false
noncomputable section

universe uC uO

def Tree (C : Type uC) (O : Type uO) : ℕ → Type (max uC uO)
  | 0 => PUnit
  | n+1 => C × (O → Tree C O n)

instance tree_fintype {C O : Type*} [Fintype C] [Fintype O] (n : ℕ) : Fintype (Tree C O n) := by
  classical
  induction n with
  | zero => change Fintype PUnit; infer_instance
  | succ n ih =>
      change Fintype (C × (O → Tree C O n))
      letI := ih
      infer_instance

instance tree_nonempty {C O : Type*} [Nonempty C] (n : ℕ) : Nonempty (Tree C O n) := by
  induction n with
  | zero => change Nonempty PUnit; infer_instance
  | succ n ih =>
      change Nonempty (C × (O → Tree C O n))
      letI := ih
      infer_instance

def argmax {D : Type*} [Fintype D] [Nonempty D] (f : D → ℝ) : D :=
  Classical.choose (Finset.exists_max_image Finset.univ f Finset.univ_nonempty)

theorem argmax_spec {D : Type*} [Fintype D] [Nonempty D] (f : D → ℝ) (d : D) :
    f d ≤ f (argmax f) :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ f Finset.univ_nonempty)).2
    d (Finset.mem_univ d)

def finiteMax {D : Type*} [Fintype D] [Nonempty D] (f : D → ℝ) : ℝ := f (argmax f)

theorem le_finiteMax {D : Type*} [Fintype D] [Nonempty D] (f : D → ℝ) (d : D) :
    f d ≤ finiteMax f := argmax_spec f d

theorem finiteMax_le {D : Type*} [Fintype D] [Nonempty D] (f : D → ℝ) (a : ℝ)
    (h : ∀ d, f d ≤ a) : finiteMax f ≤ a := h (argmax f)

@[simp] theorem finiteMax_const {D : Type*} [Fintype D] [Nonempty D] (a : ℝ) :
    finiteMax (fun _ : D => a) = a := rfl

variable {Z C O : Type*} [Fintype Z] [Fintype C] [Fintype O] [Nonempty C]

namespace Model
variable (M : Model Z C O)

/-- The alpha-vector of an actual finite contingent plan. -/
def alpha (R : Z → ℝ) : (n : ℕ) → ℕ → Tree C O n → Z → ℝ
  | 0, _, _ => R
  | n+1, t, p => M.step t p.1 (fun o => alpha R n (t+1) (p.2 o))

def score (t : ℕ) (v : Distribution Z → ℝ) (b : Distribution Z) (c : C) : ℝ :=
  ∑ o, M.branchMass t b c o * v (M.posterior t b c o)

/-- Remaining horizon and chronological time are distinct. -/
def value (R : Z → ℝ) : ℕ → ℕ → Distribution Z → ℝ
  | 0, _, b => b.dot R
  | n+1, t, b => finiteMax (fun c => M.score t (value R n (t+1)) b c)

def chosenControl (R : Z → ℝ) (n t : ℕ) (b : Distribution Z) : C :=
  argmax (fun c => M.score t (M.value R n (t+1)) b c)

def optimalTree (R : Z → ℝ) : (n : ℕ) → ℕ → Distribution Z → Tree C O n
  | 0, _, _ => PUnit.unit
  | n+1, t, b =>
      let c := M.chosenControl R n t b
      (c, fun o => optimalTree R n (t+1) (M.posterior t b c o))

theorem alpha_le_value (R : Z → ℝ) (n : ℕ) :
    ∀ (t : ℕ) (b : Distribution Z) (p : Tree C O n),
      b.dot (M.alpha R n t p) ≤ M.value R n t b := by
  induction n with
  | zero => intro t b p; exact le_rfl
  | succ n ih =>
      intro t b p
      change b.dot (M.step t p.1 (fun o => M.alpha R n (t+1) (p.2 o))) ≤
        finiteMax (fun c => M.score t (M.value R n (t+1)) b c)
      rw [M.dot_step]
      calc
        _ ≤ ∑ o, M.branchMass t b p.1 o * M.value R n (t+1) (M.posterior t b p.1 o) := by
          apply Finset.sum_le_sum
          intro o _
          exact mul_le_mul_of_nonneg_left (ih (t+1) (M.posterior t b p.1 o) (p.2 o))
            (M.branchMass_nonneg t b p.1 o)
        _ ≤ _ := le_finiteMax (fun c : C => M.score t (M.value R n (t+1)) b c) p.1

/-- Independent per-observation continuation maximizers give an attaining tree,
including arbitrary continuations on zero-probability branches. -/
theorem optimalTree_attains (R : Z → ℝ) (n : ℕ) :
    ∀ (t : ℕ) (b : Distribution Z),
      b.dot (M.alpha R n t (M.optimalTree R n t b)) = M.value R n t b := by
  induction n with
  | zero => intro t b; rfl
  | succ n ih =>
      intro t b
      change b.dot (M.step t (M.chosenControl R n t b)
        (fun o => M.alpha R n (t+1)
          (M.optimalTree R n (t+1) (M.posterior t b (M.chosenControl R n t b) o)))) = _
      rw [M.dot_step]
      simp_rw [ih]
      rfl

/-- Exact finite alpha-vector envelope. Trees are a finite index set for
Gamma; duplicate alpha-vectors do not change its maximum. -/
theorem alpha_envelope (R : Z → ℝ) (n t : ℕ) (b : Distribution Z) :
    M.value R n t b = finiteMax (fun p : Tree C O n => b.dot (M.alpha R n t p)) := by
  apply le_antisymm
  · rw [← M.optimalTree_attains R n t b]
    exact le_finiteMax (fun p : Tree C O n => b.dot (M.alpha R n t p)) (M.optimalTree R n t b)
  · exact M.alpha_le_value R n t b (argmax (fun p : Tree C O n => b.dot (M.alpha R n t p)))

/-- The finite envelope equals one linear form on each optimality cell. -/
theorem linear_on_optimal_cell (R : Z → ℝ) (n t : ℕ) (b : Distribution Z)
    (p : Tree C O n)
    (h : ∀ q : Tree C O n, b.dot (M.alpha R n t q) ≤ b.dot (M.alpha R n t p)) :
    M.value R n t b = b.dot (M.alpha R n t p) := by
  apply le_antisymm
  · rw [M.alpha_envelope]
    exact finiteMax_le _ _ h
  · exact M.alpha_le_value R n t b p

/-- Convexity on the belief simplex follows from the finite linear envelope. -/
theorem value_convex (R : Z → ℝ) (n t : ℕ) (b d : Distribution Z)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    M.value R n t (Distribution.mix θ hθ hθ1 b d) ≤
      (1-θ) * M.value R n t b + θ * M.value R n t d := by
  let e := Distribution.mix θ hθ hθ1 b d
  let p := M.optimalTree R n t e
  calc
    M.value R n t e = e.dot (M.alpha R n t p) := (M.optimalTree_attains R n t e).symm
    _ = (1-θ) * b.dot (M.alpha R n t p) + θ * d.dot (M.alpha R n t p) :=
      Distribution.dot_mix θ hθ hθ1 b d _
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (M.alpha_le_value R n t b p) (sub_nonneg.mpr hθ1))
      (mul_le_mul_of_nonneg_left (M.alpha_le_value R n t d p) hθ)

end Model
end
end PermanssonResearch.ReverseSolver.Belief
