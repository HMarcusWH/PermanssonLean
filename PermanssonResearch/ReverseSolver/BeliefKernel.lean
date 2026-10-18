import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

/-! D-BELIEF: finite hidden augmented states, common finite controls and
observations. `Z` includes every event monitor. Observations are sampled after
the controlled transition. A fixed default belief is used only on zero-mass
branches. Real vectors below export genuine probability measures. -/

open MeasureTheory
open scoped ENNReal

namespace PermanssonResearch.ReverseSolver.Belief

set_option autoImplicit false
noncomputable section

structure Distribution (D : Type*) [Fintype D] where
  weight : D → ℝ
  nonneg : ∀ d, 0 ≤ weight d
  sum_one : ∑ d, weight d = 1

namespace Distribution
variable {D : Type*} [Fintype D]

noncomputable def pure (d : D) : Distribution D := by
  classical
  exact ⟨fun e => if e = d then 1 else 0, fun e => by split_ifs <;> norm_num, by simp⟩

noncomputable def pmf (b : Distribution D) : PMF D :=
  PMF.ofFintype (fun d => ENNReal.ofReal (b.weight d)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun d _ => b.nonneg d), b.sum_one]
    norm_num)

@[simp] theorem pmf_apply (b : Distribution D) (d : D) :
    b.pmf d = ENNReal.ofReal (b.weight d) := rfl

def dot (b : Distribution D) (v : D → ℝ) : ℝ := ∑ d, b.weight d * v d

/-- The scalar finite expectation is the integral under the actual PMF law. -/
theorem integral_eq_dot [MeasurableSpace D] [MeasurableSingletonClass D]
    (b : Distribution D) (v : D → ℝ) :
    (∫ d, v d ∂b.pmf.toMeasure) = b.dot v := by
  rw [PMF.integral_eq_sum]
  simp [dot, ENNReal.toReal_ofReal, b.nonneg, smul_eq_mul]

def mix (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (b d : Distribution D) : Distribution D where
  weight z := (1-θ) * b.weight z + θ * d.weight z
  nonneg z := add_nonneg (mul_nonneg (sub_nonneg.mpr hθ1) (b.nonneg z))
    (mul_nonneg hθ (d.nonneg z))
  sum_one := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, b.sum_one, d.sum_one]
    ring

theorem dot_mix (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (b d : Distribution D) (v : D → ℝ) :
    (mix θ hθ hθ1 b d).dot v = (1-θ) * b.dot v + θ * d.dot v := by
  simp only [dot, mix, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

end Distribution

variable {Z C O : Type*} [Fintype Z] [Fintype C] [Fintype O]

/-- Every control in `C` is legal at every observable history. A declared
common menu can be represented by its finite subtype. No hidden state is
passed to the controller. -/
structure Model (Z C O : Type*) [Fintype Z] [Fintype C] [Fintype O] where
  transition : ℕ → Z → C → Distribution Z
  observation : ℕ → Z → C → Distribution O
  default : Distribution Z

namespace Model
variable (M : Model Z C O)

def numerator (t : ℕ) (b : Distribution Z) (c : C) (o : O) (z' : Z) : ℝ :=
  (M.observation t z' c).weight o *
    ∑ z, b.weight z * (M.transition t z c).weight z'

def branchMass (t : ℕ) (b : Distribution Z) (c : C) (o : O) : ℝ :=
  ∑ z', M.numerator t b c o z'

theorem numerator_nonneg (t : ℕ) (b : Distribution Z) (c : C) (o : O) (z' : Z) :
    0 ≤ M.numerator t b c o z' := by
  exact mul_nonneg ((M.observation t z' c).nonneg o)
    (Finset.sum_nonneg (fun z _ => mul_nonneg (b.nonneg z) ((M.transition t z c).nonneg z')))

theorem branchMass_nonneg (t : ℕ) (b : Distribution Z) (c : C) (o : O) :
    0 ≤ M.branchMass t b c o :=
  Finset.sum_nonneg (fun z _ => M.numerator_nonneg t b c o z)

theorem branchMass_sum (t : ℕ) (b : Distribution Z) (c : C) :
    ∑ o, M.branchMass t b c o = 1 := by
  simp only [branchMass, numerator]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, Distribution.sum_one, one_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, Distribution.sum_one, mul_one]
  exact b.sum_one

theorem numerator_eq_zero_of_branch_zero (t : ℕ) (b : Distribution Z) (c : C) (o : O)
    (hp : M.branchMass t b c o = 0) (z : Z) : M.numerator t b c o z = 0 := by
  have hle : M.numerator t b c o z ≤ M.branchMass t b c o :=
    Finset.single_le_sum (fun w _ => M.numerator_nonneg t b c o w) (Finset.mem_univ z)
  exact le_antisymm (hp ▸ hle) (M.numerator_nonneg t b c o z)

noncomputable def posterior (t : ℕ) (b : Distribution Z) (c : C) (o : O) : Distribution Z := by
  classical
  exact if hp : M.branchMass t b c o = 0 then M.default else
    { weight := fun z => M.numerator t b c o z / M.branchMass t b c o
      nonneg := fun z => div_nonneg (M.numerator_nonneg t b c o z) (M.branchMass_nonneg t b c o)
      sum_one := by rw [← Finset.sum_div]; exact div_self hp }

theorem posterior_formula (t : ℕ) (b : Distribution Z) (c : C) (o : O)
    (hp : M.branchMass t b c o ≠ 0) (z : Z) :
    (M.posterior t b c o).weight z = M.numerator t b c o z / M.branchMass t b c o := by
  simp [posterior, hp]

theorem posterior_zero (t : ℕ) (b : Distribution Z) (c : C) (o : O)
    (hp : M.branchMass t b c o = 0) : M.posterior t b c o = M.default := by
  simp [posterior, hp]

/-- The Bayes identity also holds on unsupported branches: both sides vanish. -/
theorem posterior_cancel (t : ℕ) (b : Distribution Z) (c : C) (o : O) (z : Z) :
    M.branchMass t b c o * (M.posterior t b c o).weight z = M.numerator t b c o z := by
  classical
  by_cases hp : M.branchMass t b c o = 0
  · rw [hp, zero_mul, M.numerator_eq_zero_of_branch_zero t b c o hp z]
  · rw [M.posterior_formula t b c o hp z]
    exact mul_div_cancel₀ _ hp

theorem posterior_dot_cancel (t : ℕ) (b : Distribution Z) (c : C) (o : O) (v : Z → ℝ) :
    M.branchMass t b c o * (M.posterior t b c o).dot v =
      ∑ z, M.numerator t b c o z * v z := by
  simp only [Distribution.dot, Finset.mul_sum, ← mul_assoc, M.posterior_cancel]

def jointStep (t : ℕ) (b : Distribution Z) (c : C) : Distribution (O × Z) where
  weight q := M.numerator t b c q.1 q.2
  nonneg q := M.numerator_nonneg t b c q.1 q.2
  sum_one := by
    rw [Fintype.sum_prod_type]
    exact M.branchMass_sum t b c

/-- The actual joint observation/hidden-state atom is the declared predictive
finite sum. The posterior is its conditional law on every positive branch. -/
theorem jointStep_atom (t : ℕ) (b : Distribution Z) (c : C) (o : O) (z' : Z) :
    (M.jointStep t b c).pmf (o,z') = ENNReal.ofReal
      ((M.observation t z' c).weight o * ∑ z, b.weight z * (M.transition t z c).weight z') := rfl

def step (t : ℕ) (c : C) (v : O → Z → ℝ) (z : Z) : ℝ :=
  ∑ z', (M.transition t z c).weight z' *
    ∑ o, (M.observation t z' c).weight o * v o z'

theorem sum_flip_three {D E F : Type*} [Fintype D] [Fintype E] [Fintype F]
    (f : D → E → F → ℝ) :
    (∑ d, ∑ e, ∑ g, f d e g) = ∑ g, ∑ e, ∑ d, f d e g := by
  calc
    _ = ∑ e, ∑ d, ∑ g, f d e g := Finset.sum_comm
    _ = ∑ e, ∑ g, ∑ d, f d e g := by
      apply Finset.sum_congr rfl
      intro e _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem dot_step_numerator (t : ℕ) (b : Distribution Z) (c : C) (v : O → Z → ℝ) :
    b.dot (M.step t c v) = ∑ o, ∑ z', M.numerator t b c o z' * v o z' := by
  simp only [Distribution.dot, step, numerator]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [sum_flip_three]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro z' _
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Cancellation of Bayes denominators against actual observation weights. -/
theorem dot_step (t : ℕ) (b : Distribution Z) (c : C) (v : O → Z → ℝ) :
    b.dot (M.step t c v) =
      ∑ o, M.branchMass t b c o * (M.posterior t b c o).dot (v o) := by
  rw [M.dot_step_numerator]
  apply Finset.sum_congr rfl
  intro o _
  exact (M.posterior_dot_cancel t b c o (v o)).symm

end Model
end
end PermanssonResearch.ReverseSolver.Belief
