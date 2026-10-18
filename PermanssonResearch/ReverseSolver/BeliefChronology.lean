import PermanssonResearch.ReverseSolver.BeliefFilter

/-! Literal observable-word/hidden-endpoint marginals of the independently
sampled chronological PMF. These bridge the filter to the actual history law. -/

open MeasureTheory
open scoped Classical

namespace PermanssonResearch.ReverseSolver.Belief

set_option autoImplicit false
noncomputable section

variable {Z C O : Type*} [Fintype Z] [Fintype C] [Fintype O] [Nonempty C]

def Samples.observable : (n : ℕ) → Samples Z C O n → List (C × O)
  | 0, _ => []
  | n+1, s => (s.1,s.2.1) :: Samples.observable n s.2.2.2

namespace Model
variable (M : Model Z C O)

def wordContinuation (σ : ObservationPolicy C O) (t : ℕ) (h w : List (C × O))
    (z zN : Z) : ℝ := by
  classical
  exact ∑ s : Samples Z C O w.length,
    if Samples.observable w.length s = w ∧ Model.terminal w.length z s = zN then
      M.sampleMass w.length t (σ.unfold w.length t h) z s else 0

theorem wordContinuation_nil (σ : ObservationPolicy C O) (t : ℕ) (h : List (C × O))
    (z zN : Z) : M.wordContinuation σ t h [] z zN = if z = zN then 1 else 0 := by
  classical
  unfold wordContinuation
  change (∑ s : PUnit, if ([] : List (C × O)) = [] ∧ z = zN then (1 : ℝ) else 0) = _
  simp

theorem wordContinuation_cons (σ : ObservationPolicy C O) (t : ℕ) (h w : List (C × O))
    (c : C) (o : O) (z zN : Z) :
    M.wordContinuation σ t h ((c,o)::w) z zN = (σ.choose t h).weight c *
      ∑ z', (M.transition t z c).weight z' * (M.observation t z' c).weight o *
        M.wordContinuation σ (t+1) (h ++ [(c,o)]) w z' zN := by
  classical
  change (∑ s : C × (O × (Z × Samples Z C O w.length)),
    if Samples.observable (w.length+1) s = (c,o)::w ∧
        Model.terminal (w.length+1) z s = zN then
      M.sampleMass (w.length+1) t (σ.unfold (w.length+1) t h) z s else 0) = _
  simp only [wordContinuation, List.length_cons, Fintype.sum_prod_type,
    Samples.observable, terminal, sampleMass, ObservationPolicy.unfold,
    List.cons.injEq, Prod.mk.injEq, and_assoc]
  simp_rw [ite_and, Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z' _
  apply Finset.sum_congr rfl
  intro s _
  by_cases ho : Samples.observable w.length s = w <;>
    by_cases hz : Model.terminal w.length z' s = zN <;> simp [ho,hz] <;> ring

def endpointSum (σ : ObservationPolicy C O) (t : ℕ) (h : List (C × O))
    (f : Z → ℝ) (w : List (C × O)) (zN : Z) : ℝ :=
  ∑ z, f z * M.wordContinuation σ t h w z zN

theorem endpointSum_cons (σ : ObservationPolicy C O) (t : ℕ) (h w : List (C × O))
    (f : Z → ℝ) (c : C) (o : O) (zN : Z) :
    M.endpointSum σ t h f ((c,o)::w) zN =
      M.endpointSum σ (t+1) (h ++ [(c,o)])
        (fun z' => (σ.choose t h).weight c * M.forwardStep t f c o z') w zN := by
  simp only [endpointSum]
  simp_rw [M.wordContinuation_cons, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [forwardStep, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z' _
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem endpointSum_eq_observedForward (σ : ObservationPolicy C O) (w : List (C × O)) :
    ∀ (t : ℕ) (h : List (C × O)) (f : Z → ℝ) (zN : Z),
      M.endpointSum σ t h f w zN = M.observedForward σ t h f w zN := by
  classical
  induction w with
  | nil => intro t h f zN; simp [endpointSum, M.wordContinuation_nil, observedForward, mul_ite]
  | cons a w ih =>
      intro t h f zN
      rw [M.endpointSum_cons, ih]
      rfl

theorem chronological_endpoint_integral [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (σ : ObservationPolicy C O) (t : ℕ) (h : List (C × O)) (b : Distribution Z)
    (w : List (C × O)) (zN : Z) :
    (∫ q, (if Samples.observable w.length q.2 = w ∧ Model.terminal w.length q.1 q.2 = zN
      then (1 : ℝ) else 0)
      ∂(M.chronologicalLaw w.length t b (σ.unfold w.length t h)).pmf.toMeasure) =
        M.endpointSum σ t h b.weight w zN := by
  classical
  rw [Distribution.integral_eq_dot]
  simp only [Distribution.dot, chronologicalLaw, endpointSum, wordContinuation]
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro s _
  by_cases hp : Samples.observable w.length s = w ∧ Model.terminal w.length z s = zN <;>
    simp [hp]

/-- Actual joint marginal probability of the whole observable word and the
final hidden augmented state. This is not a separately postulated filter law. -/
theorem chronological_filtered_endpoint [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (σ : ObservationPolicy C O) (t : ℕ) (h : List (C × O)) (b : Distribution Z)
    (w : List (C × O)) (zN : Z) :
    (∫ q, (if Samples.observable w.length q.2 = w ∧ Model.terminal w.length q.1 q.2 = zN
      then (1 : ℝ) else 0)
      ∂(M.chronologicalLaw w.length t b (σ.unfold w.length t h)).pmf.toMeasure) =
        (actionWeight σ t h w * M.likelihood t b w) * (M.filter t b w).weight zN := by
  rw [M.chronological_endpoint_integral, M.endpointSum_eq_observedForward,
    M.observed_filter_law]

theorem chronological_word_integral [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (σ : ObservationPolicy C O) (t : ℕ) (h : List (C × O)) (b : Distribution Z)
    (w : List (C × O)) :
    (∫ q, (if Samples.observable w.length q.2 = w then (1 : ℝ) else 0)
      ∂(M.chronologicalLaw w.length t b (σ.unfold w.length t h)).pmf.toMeasure) =
        actionWeight σ t h w * M.likelihood t b w := by
  classical
  let d := M.chronologicalLaw w.length t b (σ.unfold w.length t h)
  have hp (q : Z × Samples Z C O w.length) :
      (if Samples.observable w.length q.2 = w then (1 : ℝ) else 0) =
        ∑ zN, if Samples.observable w.length q.2 = w ∧
          Model.terminal w.length q.1 q.2 = zN then (1 : ℝ) else 0 := by
    by_cases ho : Samples.observable w.length q.2 = w <;> simp [ho]
  calc
    _ = d.dot (fun q => ∑ zN, if Samples.observable w.length q.2 = w ∧
        Model.terminal w.length q.1 q.2 = zN then (1 : ℝ) else 0) := by
      rw [Distribution.integral_eq_dot]
      simp_rw [hp]
      rfl
    _ = ∑ zN, d.dot (fun q => if Samples.observable w.length q.2 = w ∧
        Model.terminal w.length q.1 q.2 = zN then (1 : ℝ) else 0) := by
      simp only [Distribution.dot, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ zN, (actionWeight σ t h w * M.likelihood t b w) *
        (M.filter t b w).weight zN := by
      apply Finset.sum_congr rfl
      intro zN _
      rw [← Distribution.integral_eq_dot]
      exact M.chronological_filtered_endpoint σ t h b w zN
    _ = _ := by rw [← Finset.mul_sum, Distribution.sum_one, mul_one]

/-- Bayes filtering is the actual hidden endpoint conditional on a positive
probability observable history, for every real behavioral history policy. -/
theorem actual_history_conditional [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (σ : ObservationPolicy C O) (t : ℕ) (h : List (C × O)) (b : Distribution Z)
    (w : List (C × O)) (zN : Z)
    (hp : actionWeight σ t h w * M.likelihood t b w ≠ 0) :
    (∫ q, (if Samples.observable w.length q.2 = w ∧ Model.terminal w.length q.1 q.2 = zN
      then (1 : ℝ) else 0)
      ∂(M.chronologicalLaw w.length t b (σ.unfold w.length t h)).pmf.toMeasure) /
    (∫ q, (if Samples.observable w.length q.2 = w then (1 : ℝ) else 0)
      ∂(M.chronologicalLaw w.length t b (σ.unfold w.length t h)).pmf.toMeasure) =
        (M.filter t b w).weight zN := by
  rw [M.chronological_filtered_endpoint, M.chronological_word_integral]
  exact mul_div_cancel_left₀ _ hp

end Model
end
end PermanssonResearch.ReverseSolver.Belief
