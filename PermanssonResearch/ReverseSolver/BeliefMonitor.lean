import PermanssonResearch.ReverseSolver.BeliefChronology
import PermanssonResearch.ReverseSolver.FiniteMonitor
import PermanssonResearch.ReverseSolver.BehavioralFinitePolicy

/-! The finite-monitor specialization uses the full pair (physical state,
monitor state) as the hidden state. Controls are chosen from a common menu
proved legal at every hidden physical state. The physical rows are the actual
original alpha/P/U rows of the existing canonical typed realization. -/

open scoped Classical ENNReal

namespace PermanssonResearch.ReverseSolver.Belief

set_option autoImplicit false
noncomputable section

open ControlledKernel FiniteStrategicRealization

variable {C D S O : Type*} [DecidableEq C] [Fintype D] [Fintype S] [Fintype O] {n : ℕ}

structure CommonMenu (sys : FiniteControlSystem C n) (D : Type*) where
  select : D → C
  permitted : ∀ (y : Fin n) (d : D), select d ∈ sys.options y

def monitoredTransition (sys : FiniteControlSystem C n) (η : FiniteMonitor.Monitor C n S)
    (menu : CommonMenu sys D) (t : ℕ) (q : Fin n × S) (d : D) : Distribution (Fin n × S) where
  weight q' := if q'.2 = η.update t q.2 q.1 (menu.select d) q'.1 then
    ((sys.matrix (menu.select d)).entry q.1 q'.1 : ℝ) else 0
  nonneg q' := by
    split_ifs
    · exact_mod_cast (sys.matrix (menu.select d)).entry_nonneg q.1 q'.1
    · exact le_rfl
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact_mod_cast (sys.matrix (menu.select d)).row_sum_one q.1

def monitoredModel (sys : FiniteControlSystem C n) (η : FiniteMonitor.Monitor C n S)
    (menu : CommonMenu sys D) (obs : ℕ → (Fin n × S) → D → Distribution O)
    (default : Distribution (Fin n × S)) : Model (Fin n × S) D O where
  transition := monitoredTransition sys η menu
  observation := obs
  default := default

def monitoredInitial (η : FiniteMonitor.Monitor C n S) (μ : Distribution (Fin n)) :
    Distribution (Fin n × S) where
  weight q := if q.2 = η.initial q.1 then μ.weight q.1 else 0
  nonneg q := by
    split_ifs
    · exact μ.nonneg q.1
    · exact le_rfl
  sum_one := by
    rw [Fintype.sum_prod_type]
    simpa using μ.sum_one

def monitoredReward (η : FiniteMonitor.Monitor C n S) (q : Fin n × S) : ℝ := η.reward q.1 q.2

theorem monitor_transition_atom (sys : FiniteControlSystem C n) (η : FiniteMonitor.Monitor C n S)
    (menu : CommonMenu sys D) (t : ℕ) (q q' : Fin n × S) (d : D) :
    (monitoredTransition sys η menu t q d).weight q' =
      if q'.2 = η.update t q.2 q.1 (menu.select d) q'.1 then
        ((sys.matrix (menu.select d)).entry q.1 q'.1 : ℝ) else 0 := rfl

/-- The actual hidden transition retains the deterministic event-monitor
update; summing out that monitor recovers the original typed physical row. -/
theorem monitored_physical_atom (sys : FiniteControlSystem C n) (η : FiniteMonitor.Monitor C n S)
    (menu : CommonMenu sys D) (t : ℕ) (y y' : Fin n) (s : S) (d : D) :
    (∑ s', (monitoredTransition sys η menu t (y,s) d).pmf (y',s')) =
      (realizedModel (sys.matrix (menu.select d))).inducedKernel (decode y) (encode ⁻¹' {y'}) := by
  rw [inducedKernel_encodedEntry]
  simp [Distribution.pmf_apply, monitoredTransition, apply_ite]

theorem monitored_control_permitted (sys : FiniteControlSystem C n)
    (menu : CommonMenu sys D) (y : Fin n) (d : D) : menu.select d ∈ sys.options y :=
  menu.permitted y d

theorem monitored_control_world_fixed (sys : FiniteControlSystem C n)
    (menu : CommonMenu sys D) (d : D) :
    (realizedModel (sys.matrix (menu.select d))).world = (realizedModel sys.baseline).world :=
  realizedModel_world_fixed _ _

theorem monitored_control_update_fixed (sys : FiniteControlSystem C n)
    (menu : CommonMenu sys D) (d : D) :
    (realizedModel (sys.matrix (menu.select d))).generator.update =
      (realizedModel sys.baseline).generator.update := rfl

theorem monitoredInitial_support (η : FiniteMonitor.Monitor C n S) (μ : Distribution (Fin n))
    (q : Fin n × S) (hp : (monitoredInitial η μ).weight q ≠ 0) : q.2 = η.initial q.1 := by
  by_contra h
  exact hp (by simp [monitoredInitial,h])

/-- The actually realized controls and physical successors, discarding only
the observer's readout and the redundant stored monitor coordinates. -/
def physicalTrace (sys : FiniteControlSystem C n) (menu : CommonMenu sys D) :
    (r : ℕ) → Samples (Fin n × S) D O r → List (C × Fin n)
  | 0, _ => []
  | r+1, s => (menu.select s.1,s.2.2.1.1) :: physicalTrace sys menu r s.2.2.2

theorem monitor_run_on_support [Nonempty D]
    (sys : FiniteControlSystem C n) (η : FiniteMonitor.Monitor C n S)
    (menu : CommonMenu sys D) (obs : ℕ → (Fin n × S) → D → Distribution O)
    (default : Distribution (Fin n × S)) (r : ℕ) :
    ∀ (t : ℕ) (π : Behavioral D O r) (q : Fin n × S) (s : Samples (Fin n × S) D O r),
      (monitoredModel sys η menu obs default).sampleMass r t π q s ≠ 0 →
        Model.terminal r q s =
          FiniteMonitor.run η t q.1 q.2 (physicalTrace sys menu r s) := by
  induction r with
  | zero => intro t π q s hp; rfl
  | succ r ih =>
      intro t π q s hp
      change π.1.weight s.1 * (monitoredTransition sys η menu t q s.1).weight s.2.2.1 *
        (obs t s.2.2.1 s.1).weight s.2.1 *
          (monitoredModel sys η menu obs default).sampleMass r (t+1)
            (π.2 s.1 s.2.1) s.2.2.1 s.2.2.2 ≠ 0 at hp
      rcases mul_ne_zero_iff.mp hp with ⟨hbefore,htail⟩
      rcases mul_ne_zero_iff.mp hbefore with ⟨hpair,_⟩
      rcases mul_ne_zero_iff.mp hpair with ⟨_,hrow⟩
      have hguard : s.2.2.1.2 = η.update t q.2 q.1 (menu.select s.1) s.2.2.1.1 := by
        by_contra h
        exact hrow (by simp [monitoredTransition,h])
      have hrun := ih (t+1) (π.2 s.1 s.2.1) s.2.2.1 s.2.2.2 htail
      simpa only [Model.terminal,physicalTrace,FiniteMonitor.run,hguard] using hrun

/-- Literal predeclared monitor reward on the actual control/physical word;
the hidden-state monitor is proved to implement that deterministic recursion. -/
theorem monitored_integral_eq_trace_reward [Nonempty D] [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (sys : FiniteControlSystem C n) (η : FiniteMonitor.Monitor C n S)
    (menu : CommonMenu sys D) (obs : ℕ → (Fin n × S) → D → Distribution O)
    (default b : Distribution (Fin n × S)) (r t : ℕ) (π : Behavioral D O r) :
    (∫ q, monitoredReward η (Model.terminal r q.1 q.2)
      ∂((monitoredModel sys η menu obs default).chronologicalLaw r t b π).pmf.toMeasure) =
    (∫ q, monitoredReward η
      (FiniteMonitor.run η t q.1.1 q.1.2 (physicalTrace sys menu r q.2))
      ∂((monitoredModel sys η menu obs default).chronologicalLaw r t b π).pmf.toMeasure) := by
  classical
  rw [Distribution.integral_eq_dot,Distribution.integral_eq_dot]
  simp only [Distribution.dot,Model.chronologicalLaw]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hp : (monitoredModel sys η menu obs default).sampleMass r t π q.1 q.2 = 0
  · simp [hp]
  · rw [monitor_run_on_support sys η menu obs default r t π q.1 q.2 hp]

/-- With the declared monitor initialization, the literal history objective
starts at `η.initial`, including on histories of probability zero. -/
theorem monitored_initial_integral_eq_history [Nonempty D] [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (sys : FiniteControlSystem C n) (η : FiniteMonitor.Monitor C n S)
    (menu : CommonMenu sys D) (obs : ℕ → (Fin n × S) → D → Distribution O)
    (default : Distribution (Fin n × S)) (μ : Distribution (Fin n))
    (r t : ℕ) (π : Behavioral D O r) :
    (∫ q, monitoredReward η (Model.terminal r q.1 q.2)
      ∂((monitoredModel sys η menu obs default).chronologicalLaw r t
        (monitoredInitial η μ) π).pmf.toMeasure) =
    (∫ q, monitoredReward η
      (FiniteMonitor.run η t q.1.1 (η.initial q.1.1) (physicalTrace sys menu r q.2))
      ∂((monitoredModel sys η menu obs default).chronologicalLaw r t
        (monitoredInitial η μ) π).pmf.toMeasure) := by
  rw [monitored_integral_eq_trace_reward]
  rw [Distribution.integral_eq_dot,Distribution.integral_eq_dot]
  simp only [Distribution.dot,Model.chronologicalLaw]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hp : (monitoredInitial η μ).weight q.1 = 0
  · simp [hp]
  · rw [monitoredInitial_support η μ q.1 hp]

/-- All real behavioral observation histories are bounded by the belief
recursion for the original, predeclared finite-monitor objective. -/
theorem monitored_history_dominated [Nonempty D] [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (sys : FiniteControlSystem C n) (η : FiniteMonitor.Monitor C n S)
    (menu : CommonMenu sys D) (obs : ℕ → (Fin n × S) → D → Distribution O)
    (default : Distribution (Fin n × S)) (μ : Distribution (Fin n))
    (r t : ℕ) (π : Behavioral D O r) :
    (∫ q, monitoredReward η
      (FiniteMonitor.run η t q.1.1 (η.initial q.1.1) (physicalTrace sys menu r q.2))
      ∂((monitoredModel sys η menu obs default).chronologicalLaw r t
        (monitoredInitial η μ) π).pmf.toMeasure) ≤
    (monitoredModel sys η menu obs default).value (monitoredReward η) r t
      (monitoredInitial η μ) := by
  rw [← monitored_initial_integral_eq_history]
  exact Model.behavioralChronological_dominated _ _ _ _ _ _

/-- A finite observation tree attains that same literal monitor-history
objective. No physical state or hidden monitor is exposed to the controller. -/
theorem monitored_history_attained [Nonempty D] [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (sys : FiniteControlSystem C n) (η : FiniteMonitor.Monitor C n S)
    (menu : CommonMenu sys D) (obs : ℕ → (Fin n × S) → D → Distribution O)
    (default : Distribution (Fin n × S)) (μ : Distribution (Fin n)) (r t : ℕ) :
    (∫ q, monitoredReward η
      (FiniteMonitor.run η t q.1.1 (η.initial q.1.1) (physicalTrace sys menu r q.2))
      ∂((monitoredModel sys η menu obs default).chronologicalLaw r t
        (monitoredInitial η μ)
        (((monitoredModel sys η menu obs default).optimalTree (monitoredReward η) r t
          (monitoredInitial η μ)).behavioral r)).pmf.toMeasure) =
    (monitoredModel sys η menu obs default).value (monitoredReward η) r t
      (monitoredInitial η μ) := by
  rw [← monitored_initial_integral_eq_history]
  exact Model.observationTree_attains _ _ _ _ _

end
end PermanssonResearch.ReverseSolver.Belief
