import PermanssonResearch.ReverseSolver.BeliefHistory

/-! Exact filtering on complete observable action/observation words.
The unnormalized forward law is defined independently of Bayes normalization.
The product of behavioral action weights factors out because the controller
has no hidden-state argument. Zero-likelihood words have zero endpoint mass. -/

namespace PermanssonResearch.ReverseSolver.Belief

set_option autoImplicit false
noncomputable section

variable {Z C O : Type*} [Fintype Z] [Fintype C] [Fintype O] [Nonempty C]

namespace Model
variable (M : Model Z C O)

def forwardStep (t : ℕ) (f : Z → ℝ) (c : C) (o : O) (z' : Z) : ℝ :=
  (M.observation t z' c).weight o * ∑ z, f z * (M.transition t z c).weight z'

def forward : ℕ → (Z → ℝ) → List (C × O) → Z → ℝ
  | _, f, [] => f
  | t, f, a::w => forward (t+1) (M.forwardStep t f a.1 a.2) w

def filter : ℕ → Distribution Z → List (C × O) → Distribution Z
  | _, b, [] => b
  | t, b, a::w => filter (t+1) (M.posterior t b a.1 a.2) w

def likelihood : ℕ → Distribution Z → List (C × O) → ℝ
  | _, _, [] => 1
  | t, b, a::w => M.branchMass t b a.1 a.2 *
      likelihood (t+1) (M.posterior t b a.1 a.2) w

theorem forwardStep_scaled (t : ℕ) (q : ℝ) (f : Z → ℝ) (c : C) (o : O) :
    M.forwardStep t (fun z => q * f z) c o = fun z' => q * M.forwardStep t f c o z' := by
  funext z'
  simp only [forwardStep, mul_assoc, ← Finset.mul_sum]
  ring

theorem forward_scaled (w : List (C × O)) : ∀ (t : ℕ) (q : ℝ) (f : Z → ℝ),
    M.forward t (fun z => q * f z) w = fun z' => q * M.forward t f w z' := by
  induction w with
  | nil => intro t q f; rfl
  | cons a w ih =>
      intro t q f
      simp only [forward, M.forwardStep_scaled]
      exact ih (t+1) q (M.forwardStep t f a.1 a.2)

/-- The actual forward endpoint law factors into word probability and the
Bayes-filtered belief, even when the word probability is zero. -/
theorem forward_belief_scaled (w : List (C × O)) : ∀ (t : ℕ) (q : ℝ) (b : Distribution Z),
    M.forward t (fun z => q * b.weight z) w =
      fun z => q * M.likelihood t b w * (M.filter t b w).weight z := by
  induction w with
  | nil => intro t q b; funext z; simp [forward, likelihood, filter]
  | cons a w ih =>
      intro t q b
      have hstep : M.forwardStep t (fun z => q * b.weight z) a.1 a.2 =
          fun z => (q * M.branchMass t b a.1 a.2) * (M.posterior t b a.1 a.2).weight z := by
        rw [M.forwardStep_scaled]
        funext z
        change q * M.numerator t b a.1 a.2 z = _
        rw [← M.posterior_cancel t b a.1 a.2 z]
        ring
      simp only [forward, hstep]
      rw [ih]
      funext z
      simp only [likelihood, filter]
      ring

theorem forward_belief (t : ℕ) (b : Distribution Z) (w : List (C × O)) :
    M.forward t b.weight w = fun z => M.likelihood t b w * (M.filter t b w).weight z := by
  simpa using M.forward_belief_scaled w t 1 b

theorem forward_total (t : ℕ) (b : Distribution Z) (w : List (C × O)) :
    (∑ z, M.forward t b.weight w z) = M.likelihood t b w := by
  rw [M.forward_belief]
  rw [← Finset.mul_sum, Distribution.sum_one, mul_one]

theorem filtered_conditional (t : ℕ) (b : Distribution Z) (w : List (C × O))
    (hp : M.likelihood t b w ≠ 0) (z : Z) :
    M.forward t b.weight w z / M.likelihood t b w = (M.filter t b w).weight z := by
  rw [M.forward_belief]
  exact mul_div_cancel_left₀ _ hp

theorem zero_word_mass (t : ℕ) (b : Distribution Z) (w : List (C × O))
    (hp : M.likelihood t b w = 0) (z : Z) : M.forward t b.weight w z = 0 := by
  simpa [hp] using congrFun (M.forward_belief t b w) z

def actionWeight (σ : ObservationPolicy C O) : ℕ → List (C × O) → List (C × O) → ℝ
  | _, _, [] => 1
  | t, h, a::w => (σ.choose t h).weight a.1 *
      actionWeight σ (t+1) (h ++ [a]) w

/-- The independent forward law includes the behavioral weight before the
hidden transition and observation at each chronological node. -/
def observedForward (σ : ObservationPolicy C O) :
    ℕ → List (C × O) → (Z → ℝ) → List (C × O) → Z → ℝ
  | _, _, f, [] => f
  | t, h, f, a::w => observedForward σ (t+1) (h ++ [a])
      (fun z => (σ.choose t h).weight a.1 * M.forwardStep t f a.1 a.2 z) w

theorem observedForward_eq_actionWeight (σ : ObservationPolicy C O) (w : List (C × O)) :
    ∀ (t : ℕ) (h : List (C × O)) (f : Z → ℝ),
      M.observedForward σ t h f w =
        fun z => actionWeight σ t h w * M.forward t f w z := by
  induction w with
  | nil => intro t h f; funext z; simp [observedForward, actionWeight, forward]
  | cons a w ih =>
      intro t h f
      simp only [observedForward, actionWeight]
      rw [ih, M.forward_scaled]
      funext z
      simp only [forward]
      ring

theorem observed_filter_law (σ : ObservationPolicy C O) (t : ℕ)
    (h : List (C × O)) (b : Distribution Z) (w : List (C × O)) :
    M.observedForward σ t h b.weight w = fun z =>
      (actionWeight σ t h w * M.likelihood t b w) * (M.filter t b w).weight z := by
  rw [M.observedForward_eq_actionWeight, M.forward_belief]
  funext z
  ring

theorem observed_word_probability (σ : ObservationPolicy C O) (t : ℕ)
    (h : List (C × O)) (b : Distribution Z) (w : List (C × O)) :
    (∑ z, M.observedForward σ t h b.weight w z) =
      actionWeight σ t h w * M.likelihood t b w := by
  rw [M.observed_filter_law]
  rw [← Finset.mul_sum, Distribution.sum_one, mul_one]

end Model
end
end PermanssonResearch.ReverseSolver.Belief
