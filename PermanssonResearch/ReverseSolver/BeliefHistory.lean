import PermanssonResearch.ReverseSolver.BeliefAlpha

/-! Real behavioral observation-history policies and the independently
constructed chronological law. Its samples record controls, observations and
hidden successors. The policy sees only the first two of these. -/

open MeasureTheory

namespace PermanssonResearch.ReverseSolver.Belief

set_option autoImplicit false
noncomputable section

universe uZ uC uO

def Behavioral (C : Type uC) (O : Type uO) [Fintype C] : ℕ → Type (max uC uO)
  | 0 => PUnit
  | n+1 => Distribution C × (C → O → Behavioral C O n)

/-- An arbitrary real behavioral policy on all observable pasts. -/
structure ObservationPolicy (C O : Type*) [Fintype C] where
  choose : ℕ → List (C × O) → Distribution C

def ObservationPolicy.unfold {C O : Type*} [Fintype C] (σ : ObservationPolicy C O) :
    (n : ℕ) → ℕ → List (C × O) → Behavioral C O n
  | 0, _, _ => PUnit.unit
  | n+1, t, h => (σ.choose t h, fun c o => σ.unfold n (t+1) (h ++ [(c,o)]))

def Tree.behavioral {C O : Type*} [Fintype C] : (n : ℕ) → Tree C O n → Behavioral C O n
  | 0, _ => PUnit.unit
  | n+1, p => (Distribution.pure p.1, fun _ o => Tree.behavioral n (p.2 o))

namespace Distribution
theorem dot_sum {D E : Type*} [Fintype D] [Fintype E]
    (b : Distribution D) (w : E → ℝ) (v : E → D → ℝ) :
    b.dot (fun d => ∑ e, w e * v e d) = ∑ e, w e * b.dot (v e) := by
  simp only [dot, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro d _
  ring
end Distribution

variable {Z C O : Type*} [Fintype Z] [Fintype C] [Fintype O] [Nonempty C]

namespace Model
variable (M : Model Z C O)

/-- Conditional reward under the actual hidden transition and observation
rows; action weights depend on the observation-policy node, never on `z`. -/
def stateValue (R : Z → ℝ) : (n : ℕ) → ℕ → Behavioral C O n → Z → ℝ
  | 0, _, _ => R
  | n+1, t, π => fun z => ∑ c, π.1.weight c *
      M.step t c (fun o => stateValue R n (t+1) (π.2 c o)) z

def expected (R : Z → ℝ) (n t : ℕ) (b : Distribution Z) (π : Behavioral C O n) : ℝ :=
  b.dot (M.stateValue R n t π)

theorem expected_succ (R : Z → ℝ) (n t : ℕ) (b : Distribution Z)
    (π : Behavioral C O (n+1)) :
    M.expected R (n+1) t b π = ∑ c, π.1.weight c *
      ∑ o, M.branchMass t b c o * M.expected R n (t+1) (M.posterior t b c o) (π.2 c o) := by
  change b.dot (fun z => ∑ c, π.1.weight c *
    M.step t c (fun o => M.stateValue R n (t+1) (π.2 c o)) z) = _
  rw [Distribution.dot_sum]
  simp_rw [M.dot_step]
  rfl

theorem stateValue_one (n : ℕ) : ∀ (t : ℕ) (π : Behavioral C O n) (z : Z),
    M.stateValue (fun _ => 1) n t π z = 1 := by
  induction n with
  | zero => intro t π z; rfl
  | succ n ih =>
      intro t π z
      simp only [stateValue, ih]
      simp [step, Distribution.sum_one, ih]

theorem stateValue_tree (R : Z → ℝ) (n : ℕ) :
    ∀ (t : ℕ) (p : Tree C O n) (z : Z),
      M.stateValue R n t (p.behavioral n) z = M.alpha R n t p z := by
  classical
  induction n with
  | zero => intro t p z; rfl
  | succ n ih =>
      intro t p z
      simp [stateValue, Tree.behavioral, Distribution.pure, ih, alpha, step]

/-- Every real behavioral observation-policy tree is bounded by the same
belief value; this does not restrict the weights to rational probabilities. -/
theorem expected_le_value (R : Z → ℝ) (n : ℕ) :
    ∀ (t : ℕ) (b : Distribution Z) (π : Behavioral C O n),
      M.expected R n t b π ≤ M.value R n t b := by
  induction n with
  | zero => intro t b π; exact le_rfl
  | succ n ih =>
      intro t b π
      rw [M.expected_succ]
      calc
        _ ≤ ∑ c, π.1.weight c * ∑ o,
            M.branchMass t b c o * M.value R n (t+1) (M.posterior t b c o) := by
          apply Finset.sum_le_sum
          intro c _
          apply mul_le_mul_of_nonneg_left _ (π.1.nonneg c)
          apply Finset.sum_le_sum
          intro o _
          exact mul_le_mul_of_nonneg_left
            (ih (t+1) (M.posterior t b c o) (π.2 c o)) (M.branchMass_nonneg t b c o)
        _ ≤ ∑ c, π.1.weight c * M.value R (n+1) t b := by
          apply Finset.sum_le_sum
          intro c _
          exact mul_le_mul_of_nonneg_left
            (le_finiteMax (fun d => M.score t (M.value R n (t+1)) b d) c) (π.1.nonneg c)
        _ = _ := by rw [← Finset.sum_mul, π.1.sum_one, one_mul]

end Model

/-- A literal chronological control/observation/hidden-successor word. -/
def Samples (Z : Type uZ) (C : Type uC) (O : Type uO) : ℕ → Type (max uZ uC uO)
  | 0 => PUnit
  | n+1 => C × (O × (Z × Samples Z C O n))

instance samples_fintype : (n : ℕ) → Fintype (Samples Z C O n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => by
      change Fintype (C × (O × (Z × Samples Z C O n)))
      letI := samples_fintype n
      infer_instance

/-- Finite sample words carry their full discrete sigma algebra. -/
instance samples_measurable (n : ℕ) : MeasurableSpace (Samples Z C O n) := ⊤
instance samples_singletons (n : ℕ) : MeasurableSingletonClass (Samples Z C O n) :=
  ⟨fun _ => by trivial⟩

namespace Model
variable (M : Model Z C O)

def sampleMass : (n : ℕ) → ℕ → Behavioral C O n → Z → Samples Z C O n → ℝ
  | 0, _, _, _, _ => 1
  | n+1, t, π, z, s => π.1.weight s.1 * (M.transition t z s.1).weight s.2.2.1 *
      (M.observation t s.2.2.1 s.1).weight s.2.1 *
        sampleMass n (t+1) (π.2 s.1 s.2.1) s.2.2.1 s.2.2.2

def terminal : (n : ℕ) → Z → Samples Z C O n → Z
  | 0, z, _ => z
  | n+1, _, s => Model.terminal n s.2.2.1 s.2.2.2

def conditionalMean (R : Z → ℝ) (n t : ℕ) (π : Behavioral C O n) (z : Z) : ℝ :=
  ∑ s, M.sampleMass n t π z s * R (Model.terminal n z s)

theorem conditionalMean_eq_stateValue (R : Z → ℝ) (n : ℕ) :
    ∀ (t : ℕ) (π : Behavioral C O n) (z : Z),
      M.conditionalMean R n t π z = M.stateValue R n t π z := by
  induction n with
  | zero =>
      intro t π z
      change (∑ s : PUnit, (1 : ℝ) * R z) = R z
      simp
  | succ n ih =>
      intro t π z
      change (∑ s : C × (O × (Z × Samples Z C O n)),
        M.sampleMass (n+1) t π z s * R (Model.terminal (n+1) z s)) = _
      simp only [Fintype.sum_prod_type, sampleMass, terminal]
      change (∑ c, ∑ o, ∑ z', ∑ s : Samples Z C O n,
        (π.1.weight c * (M.transition t z c).weight z' * (M.observation t z' c).weight o *
          M.sampleMass n (t+1) (π.2 c o) z' s) * R (Model.terminal n z' s)) = _
      have htail (c : C) (o : O) (z' : Z) :
          (∑ s : Samples Z C O n,
            (π.1.weight c * (M.transition t z c).weight z' * (M.observation t z' c).weight o *
              M.sampleMass n (t+1) (π.2 c o) z' s) * R (Model.terminal n z' s)) =
            π.1.weight c * (M.transition t z c).weight z' * (M.observation t z' c).weight o *
              M.stateValue R n (t+1) (π.2 c o) z' := by
        rw [← ih (t+1) (π.2 c o) z']
        simp only [conditionalMean, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      simp_rw [htail]
      change _ = ∑ c, π.1.weight c * M.step t c
        (fun o => M.stateValue R n (t+1) (π.2 c o)) z
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
      simp only [step, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z' _
      apply Finset.sum_congr rfl
      intro o _
      ring

theorem sampleMass_nonneg (n : ℕ) : ∀ (t : ℕ) (π : Behavioral C O n) (z : Z)
    (s : Samples Z C O n), 0 ≤ M.sampleMass n t π z s := by
  induction n with
  | zero => intro t π z s; exact zero_le_one
  | succ n ih =>
      intro t π z s
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (π.1.nonneg s.1) ((M.transition t z s.1).nonneg s.2.2.1))
          ((M.observation t s.2.2.1 s.1).nonneg s.2.1))
        (ih (t+1) (π.2 s.1 s.2.1) s.2.2.1 s.2.2.2)

theorem sampleMass_sum (n t : ℕ) (π : Behavioral C O n) (z : Z) :
    ∑ s, M.sampleMass n t π z s = 1 := by
  have h := M.conditionalMean_eq_stateValue (fun _ => 1) n t π z
  simpa [conditionalMean, M.stateValue_one] using h

/-- The independently sampled law, including the initial hidden augmented
state. Its PMF and measure are normalized before any Bellman theorem is used. -/
def chronologicalLaw (n t : ℕ) (b : Distribution Z) (π : Behavioral C O n) :
    Distribution (Z × Samples Z C O n) where
  weight q := b.weight q.1 * M.sampleMass n t π q.1 q.2
  nonneg q := mul_nonneg (b.nonneg q.1) (M.sampleMass_nonneg n t π q.1 q.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, M.sampleMass_sum, mul_one]
    exact b.sum_one

theorem chronologicalMean_eq_expected (R : Z → ℝ) (n t : ℕ)
    (b : Distribution Z) (π : Behavioral C O n) :
    (M.chronologicalLaw n t b π).dot (fun q => R (Model.terminal n q.1 q.2)) =
      M.expected R n t b π := by
  simp only [Distribution.dot, chronologicalLaw]
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  change (∑ z, b.weight z * M.conditionalMean R n t π z) = _
  simp_rw [M.conditionalMean_eq_stateValue]
  rfl

/-- The belief evaluator equals the expectation under the actual complete
chronological word law. -/
theorem chronologicalIntegral_eq_expected [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (R : Z → ℝ) (n t : ℕ) (b : Distribution Z) (π : Behavioral C O n) :
    (∫ q, R (Model.terminal n q.1 q.2) ∂(M.chronologicalLaw n t b π).pmf.toMeasure) =
      M.expected R n t b π := by
  rw [Distribution.integral_eq_dot, M.chronologicalMean_eq_expected]

theorem observationHistory_dominated [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (R : Z → ℝ) (n t : ℕ) (b : Distribution Z) (h : List (C × O)) (σ : ObservationPolicy C O) :
    (∫ q, R (Model.terminal n q.1 q.2)
      ∂(M.chronologicalLaw n t b (σ.unfold n t h)).pmf.toMeasure) ≤ M.value R n t b := by
  rw [M.chronologicalIntegral_eq_expected]
  exact M.expected_le_value R n t b (σ.unfold n t h)

theorem behavioralChronological_dominated [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (R : Z → ℝ) (n t : ℕ) (b : Distribution Z) (π : Behavioral C O n) :
    (∫ q, R (Model.terminal n q.1 q.2)
      ∂(M.chronologicalLaw n t b π).pmf.toMeasure) ≤ M.value R n t b := by
  rw [M.chronologicalIntegral_eq_expected]
  exact M.expected_le_value R n t b π

/-- The maximizing finite observation-policy tree attains the actual optimum,
not merely the value of a separately defined scalar recurrence. -/
theorem observationTree_attains [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (R : Z → ℝ) (n t : ℕ) (b : Distribution Z) :
    (∫ q, R (Model.terminal n q.1 q.2)
      ∂(M.chronologicalLaw n t b ((M.optimalTree R n t b).behavioral n)).pmf.toMeasure) =
        M.value R n t b := by
  rw [M.chronologicalIntegral_eq_expected]
  simp only [expected, Distribution.dot]
  simp_rw [M.stateValue_tree]
  exact M.optimalTree_attains R n t b

end Model
end
end PermanssonResearch.ReverseSolver.Belief
