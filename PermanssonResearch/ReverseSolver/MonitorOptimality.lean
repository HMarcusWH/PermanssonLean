import PermanssonResearch.ReverseSolver.BehavioralFinitePolicy

/-!
# Finite monitor optimality over all real behavioral full-history policies

The upper bound is on the independently enumerated chronological trace law.
The attaining policy reconstructs its monitor from the realized history; the
controller is never given an extra unobserved state variable.
-/

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open ControlledKernel

universe uC uS

variable {C : Type uC} [DecidableEq C] [Fintype C] {n : ℕ} {S : Type uS}

/-- Convex averaging proves the full real behavioral-history upper bound. -/
theorem monitor_value_dominates_behavioral_history
    (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (σ : BehavioralPolicy sys) (r t : ℕ) (h : TraceHistory C n)
    (y : Fin n) (s : S) :
    behavioralValue sys M σ r t h y s ≤ (value sys M r t y s : ℝ) := by
  induction r generalizing t h y s with
  | zero => exact le_rfl
  | succ r ih =>
      change (∑ c : C, σ.weight t h y c *
        ∑ z : Fin n, ((sys.matrix c).entry y z : ℝ) *
          behavioralValue sys M σ r (t+1) (appendTrace h c z) z (M.update t s y c z)) ≤ _
      calc
        _ ≤ ∑ c : C, σ.weight t h y c *
              (score sys M (value sys M r (t+1)) t y s c : ℝ) := by
          apply Finset.sum_le_sum
          intro c _
          apply mul_le_mul_of_nonneg_left _ (σ.nonnegative t h y c)
          simp only [score, Rat.cast_sum, Rat.cast_mul]
          apply Finset.sum_le_sum
          intro z _
          apply mul_le_mul_of_nonneg_left (ih (t+1) (appendTrace h c z) z _)
          exact_mod_cast (sys.matrix c).entry_nonneg y z
        _ ≤ ∑ c : C, σ.weight t h y c * (value sys M (r+1) t y s : ℝ) := by
          apply Finset.sum_le_sum
          intro c _
          by_cases hc : c ∈ sys.options y
          · apply mul_le_mul_of_nonneg_left _ (σ.nonnegative t h y c)
            exact_mod_cast maximizingControl_dominates sys M
              (value sys M r (t+1)) t y s c hc
          · simp [σ.supported t h y c hc]
        _ = (value sys M (r+1) t y s : ℝ) := by
          rw [← Finset.sum_mul, σ.normalized, one_mul]

/-- Same upper bound, stated directly for the actual chronological word law. -/
theorem monitor_trace_value_dominates_behavioral_history
    (sys : FiniteControlSystem C n) (M : Monitor C n S)
    (σ : BehavioralPolicy sys) (r t : ℕ) (h : TraceHistory C n)
    (y : Fin n) (s : S) :
    traceExpectation sys M σ r t h y s ≤ (value sys M r t y s : ℝ) := by
  rw [traceExpectation_eq_behavioralValue]
  exact monitor_value_dominates_behavioral_history sys M σ r t h y s

/-- Embed a deterministic monitor controller into the allowed history class.
Its monitor state is calculated from the recorded past controls and states. -/
noncomputable def realizedPolicy (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (π : MonitorPolicy sys S) : BehavioralPolicy sys where
  weight t h y c := if c = π.choose t y
      (run M 0 h.1 (M.initial h.1) h.2).2 then 1 else 0
  nonnegative t h y c := by split <;> norm_num
  normalized t h y := by simp
  supported t h y c hc := by
    have hn : c ≠ π.choose t y (run M 0 h.1 (M.initial h.1) h.2).2 := by
      intro he
      exact hc (he ▸ π.permitted t y _)
    simp [hn]

theorem realizedPolicy_value (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (π : MonitorPolicy sys S) (r : ℕ)
    (h : TraceHistory C n) :
    behavioralValue sys M (realizedPolicy sys M π) r h.2.length h
      (run M 0 h.1 (M.initial h.1) h.2).1
      (run M 0 h.1 (M.initial h.1) h.2).2 =
    (deterministicValue sys M π r h.2.length
      (run M 0 h.1 (M.initial h.1) h.2).1
      (run M 0 h.1 (M.initial h.1) h.2).2 : ℝ) := by
  induction r generalizing h with
  | zero => rfl
  | succ r ih =>
      let y := (run M 0 h.1 (M.initial h.1) h.2).1
      let s := (run M 0 h.1 (M.initial h.1) h.2).2
      let c := π.choose h.2.length y s
      have ha (z : Fin n) :
          run M 0 (appendTrace h c z).1 (M.initial (appendTrace h c z).1)
            (appendTrace h c z).2 = (z, M.update h.2.length s y c z) := by
        simp only [appendTrace, run_append, zero_add, List.length_singleton, run]
        rfl
      change (∑ a : C, (if a = c then (1 : ℝ) else 0) *
        ∑ z : Fin n, ((sys.matrix a).entry y z : ℝ) *
          behavioralValue sys M (realizedPolicy sys M π) r (h.2.length+1)
            (appendTrace h a z) z (M.update h.2.length s y a z)) = _
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, deterministicValue, Rat.cast_sum, Rat.cast_mul]
      apply Finset.sum_congr rfl
      intro z _
      have hz := ih (appendTrace h c z)
      have hlen : (appendTrace h c z).2.length = h.2.length+1 := by simp [appendTrace]
      rw [hlen] at hz
      simp only [ha, Prod.fst, Prod.snd] at hz
      rw [hz]

/-- An actual behavioral full-history policy attains the monitor optimum. -/
theorem monitor_behavioral_maximizer_attains
    (sys : FiniteControlSystem C n) (M : Monitor C n S) (N : ℕ) (y : Fin n) :
    traceExpectation sys M (realizedPolicy sys M (deterministicMaximizer sys M N))
      N 0 (y,[]) y (M.initial y) = (value sys M N 0 y (M.initial y) : ℝ) := by
  rw [traceExpectation_eq_behavioralValue]
  have h := realizedPolicy_value sys M (deterministicMaximizer sys M N) N (y,[])
  simp only [List.length_nil, run] at h
  rw [h, monitor_deterministic_maximizer_attains sys M N N 0 y _ (by omega)]

/-- The Bellman value is an upper bound and is attained in precisely the same
full-history behavioral class, with arbitrary real mixing probabilities. -/
theorem monitor_optimal_and_attained (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (N : ℕ) (y : Fin n) :
    (∀ σ : BehavioralPolicy sys, traceExpectation sys M σ N 0 (y,[]) y (M.initial y)
      ≤ (value sys M N 0 y (M.initial y) : ℝ)) ∧
    (∃ σ : BehavioralPolicy sys, traceExpectation sys M σ N 0 (y,[]) y (M.initial y)
      = (value sys M N 0 y (M.initial y) : ℝ)) := by
  exact ⟨fun σ => monitor_trace_value_dominates_behavioral_history sys M σ N 0 _ y _,
    ⟨_, monitor_behavioral_maximizer_attains sys M N y⟩⟩

end PermanssonResearch.ReverseSolver.FiniteMonitor
