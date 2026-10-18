import PermanssonResearch.ReverseSolver.ChronologicalMonitorMeasure

/-! The actual chronological product law and simultaneous optimal policy for
an arbitrary finite real initial probability law. -/

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open ControlledKernel

variable {C S : Type*} [DecidableEq C] [Fintype C] {n : ℕ}

noncomputable def initialChronologicalLaw (sys : FiniteControlSystem C n)
    (σ : BehavioralPolicy sys) (μ : FiniteProbabilityLaw (Fin n)) (N : ℕ) :
    FiniteProbabilityLaw (Fin n × List (C × Fin n)) where
  support := μ.support.product (traceWords C n N).toFinset
  atom a := μ.atom a.1*(chronologicalLaw sys σ N 0 (a.1,[]) a.1).atom a.2
  nonnegative a := mul_nonneg (μ.nonnegative a.1)
    ((chronologicalLaw sys σ N 0 (a.1,[]) a.1).nonnegative a.2)
  supported a ha := by
    by_cases hy : a.1 ∈ μ.support
    · have hx : a.2 ∉ (traceWords C n N).toFinset := by
        intro hx
        exact ha (Finset.mem_product.mpr ⟨hy,hx⟩)
      rw [(chronologicalLaw sys σ N 0 (a.1,[]) a.1).supported a.2 hx,mul_zero]
    · rw [μ.supported a.1 hy,zero_mul]
  normalized := by
    rw [Finset.product_eq_sprod]
    rw [Finset.sum_product μ.support (traceWords C n N).toFinset
      (fun a : Fin n × List (C × Fin n) =>
        μ.atom a.1*(chronologicalLaw sys σ N 0 (a.1,[]) a.1).atom a.2)]
    calc
      _ = ∑ y ∈ μ.support, μ.atom y*1 := by
        apply Finset.sum_congr rfl
        intro y _
        change (∑ xs ∈ (traceWords C n N).toFinset,
          μ.atom y*(chronologicalLaw sys σ N 0 (y,[]) y).atom xs)=μ.atom y*1
        rw [← Finset.mul_sum]
        exact congrArg (fun x => μ.atom y*x)
          (chronologicalLaw sys σ N 0 (y,[]) y).normalized
      _ = 1 := by simpa using μ.normalized

def initialMonitorReward (M : Monitor C n S)
    (a : Fin n × List (C × Fin n)) : ℝ :=
  (M.reward (run M 0 a.1 (M.initial a.1) a.2).1
    (run M 0 a.1 (M.initial a.1) a.2).2 : ℝ)

theorem initialChronologicalLaw_monitor_expectation (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (σ : BehavioralPolicy sys)
    (μ : FiniteProbabilityLaw (Fin n)) (N : ℕ) :
    (initialChronologicalLaw sys σ μ N).expectation (initialMonitorReward M)=
      μ.expectation (fun y => traceExpectation sys M σ N 0 (y,[]) y (M.initial y)) := by
  unfold FiniteProbabilityLaw.expectation
  change (∑ a ∈ μ.support.product (traceWords C n N).toFinset,
      μ.atom a.1*(chronologicalLaw sys σ N 0 (a.1,[]) a.1).atom a.2*
        initialMonitorReward M a)=_
  rw [Finset.product_eq_sprod]
  rw [Finset.sum_product μ.support (traceWords C n N).toFinset
    (fun a : Fin n × List (C × Fin n) =>
      μ.atom a.1*(chronologicalLaw sys σ N 0 (a.1,[]) a.1).atom a.2*
        initialMonitorReward M a)]
  apply Finset.sum_congr rfl
  intro y _
  change (∑ xs ∈ (traceWords C n N).toFinset,
    μ.atom y*(chronologicalLaw sys σ N 0 (y,[]) y).atom xs*
      initialMonitorReward M (y,xs))=
        μ.atom y*traceExpectation sys M σ N 0 (y,[]) y (M.initial y)
  rw [← chronologicalLaw_monitor_expectation]
  unfold FiniteProbabilityLaw.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xs _
  simp only [initialMonitorReward]
  ring

/-- One admissible deterministic time/state/monitor policy attains the
expected value for every initial law, with arbitrary real initial atoms. -/
theorem monitor_initialLaw_optimal_and_attained (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (μ : FiniteProbabilityLaw (Fin n)) (N : ℕ) :
    (∀ σ : BehavioralPolicy sys,
      (initialChronologicalLaw sys σ μ N).expectation (initialMonitorReward M)≤
        μ.expectation (fun y => (value sys M N 0 y (M.initial y) : ℝ))) ∧
    (initialChronologicalLaw sys
        (realizedPolicy sys M (deterministicMaximizer sys M N)) μ N).expectation
      (initialMonitorReward M)=
        μ.expectation (fun y => (value sys M N 0 y (M.initial y) : ℝ)) := by
  simp only [initialChronologicalLaw_monitor_expectation]
  constructor
  · intro σ
    apply Finset.sum_le_sum
    intro y _
    exact mul_le_mul_of_nonneg_left
      (monitor_trace_value_dominates_behavioral_history sys M σ N 0 _ y _) (μ.nonnegative y)
  · simp_rw [monitor_behavioral_maximizer_attains]

end PermanssonResearch.ReverseSolver.FiniteMonitor
