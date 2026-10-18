import PermanssonResearch.ReverseSolver.FiniteOccupancyHistory

/-! Ordinary event probabilities for the actual finite full-history laws.
The state/control arrays are genuine probability marginals. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace PermanssonResearch.ReverseSolver.Occupancy
open ActionTrace
noncomputable section

theorem row_event_probability {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (p : Row A) (P : A → Prop) [DecidablePred P] :
    p.measure {a | P a}=ENNReal.ofReal (p.expect (fun a => if P a then 1 else 0)) := by
  have hS : MeasurableSet {a | P a} := (Set.to_countable _).measurableSet
  have hi : p.expect (fun a => if P a then 1 else 0)=p.measure.real {a | P a} := by
    rw [Row.expect_eq_integral]
    simpa [Set.indicator] using (integral_indicator_one (μ := p.measure) hS)
  rw [hi,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top p.measure _)]

variable {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}

theorem actual_state_probability (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (t : ℕ) (y : Fin n) :
    actualHistoryMeasure sys σ μ t {h | last t h=y}=ENNReal.ofReal (stateMass sys σ μ t y) := by
  rw [actualHistoryMeasure,row_event_probability,← stateMass_eq_expect]

theorem actual_terminal_event_probability (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (N : ℕ) (G : Finset (Fin n)) :
    actualHistoryMeasure sys σ μ N {h | last N h ∈ G}=
      ENNReal.ofReal (∑ y ∈ G, (occupancies sys σ μ N).state (Fin.last N) y) := by
  rw [actualHistoryMeasure,row_event_probability]
  congr 1
  simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_mem,Finset.univ_inter] using
    terminal_expect_eq_occupancy sys σ μ N (fun y => if y ∈ G then 1 else 0)

section Action
variable [MeasurableSpace C] [MeasurableSingletonClass C]

def actualActionMeasure (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (t : ℕ) : Measure (Fin n × C) := (actionRow sys σ μ t).measure

instance actualActionMeasure_probability (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (t : ℕ) : IsProbabilityMeasure (actualActionMeasure sys σ μ t) := by
  unfold actualActionMeasure
  infer_instance

theorem actual_action_probability (sys : TimeSystem C n) (σ : BehavioralPolicy sys)
    (μ : Row (Fin n)) (t : ℕ) (y : Fin n) (c : C) :
    actualActionMeasure sys σ μ t {(y,c)}=ENNReal.ofReal (actionMass sys σ μ t y c) :=
  Row.measure_singleton (actionRow sys σ μ t) (y,c)

end Action
end
end PermanssonResearch.ReverseSolver.Occupancy
