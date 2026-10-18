import PermanssonResearch.ReverseSolver.FiniteOccupancyMarginals
import PermanssonResearch.ReverseSolver.BehavioralFinitePolicy

/-! Actual finite monitor/control rows as occupancy models. The original
physical row is retained literally; only a deterministic monitor is appended.
The actual finite history law is almost surely a correct monitor execution. -/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.ReverseSolver.Occupancy
open ControlledKernel ActionTrace
noncomputable section
variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]
  {n m : ℕ}

def augmentedMatrix (sys : FiniteControlSystem C n) (M : FiniteMonitor.Monitor C n S)
    (e : Fin m ≃ Fin n × S) (t : ℕ) (c : C) : RationalMarkovMatrix m where
  entry i j := if (e j).2=M.update t (e i).2 (e i).1 c (e j).1
    then (sys.matrix c).entry (e i).1 (e j).1 else 0
  entry_nonneg i j := by split <;> first | exact (sys.matrix c).entry_nonneg _ _ | exact le_rfl
  row_sum_one i := by
    calc
      (∑ j : Fin m, if (e j).2=M.update t (e i).2 (e i).1 c (e j).1
          then (sys.matrix c).entry (e i).1 (e j).1 else 0)=
          ∑ p : Fin n × S, if p.2=M.update t (e i).2 (e i).1 c p.1
            then (sys.matrix c).entry (e i).1 p.1 else 0 := by
        apply Fintype.sum_equiv e
        intro j
        rfl
      _ = ∑ z : Fin n, (sys.matrix c).entry (e i).1 z := by simp [Fintype.sum_prod_type]
      _ = 1 := (sys.matrix c).row_sum_one (e i).1

def monitorSystem (sys : FiniteControlSystem C n) (M : FiniteMonitor.Monitor C n S)
    (e : Fin m ≃ Fin n × S) : TimeSystem C m where
  states_nonempty := by
    have hh := (e.symm (⟨0,sys.states_nonempty⟩,M.initial ⟨0,sys.states_nonempty⟩)).isLt
    omega
  options _ i := sys.options (e i).1
  options_nonempty _ i := sys.options_nonempty (e i).1
  matrix t c := augmentedMatrix sys M e t c

/-- Exact action-conditioned transition identity, preserving the original
physical K and the realized-control monitor update in chronological order. -/
theorem monitor_row_expect (sys : FiniteControlSystem C n) (M : FiniteMonitor.Monitor C n S)
    (e : Fin m ≃ Fin n × S) (t : ℕ) (i : Fin m) (c : C) (v : Fin m → ℝ) :
    (matrixRow (monitorSystem sys M e) t i c).expect v=
      ∑ z : Fin n, ((sys.matrix c).entry (e i).1 z : ℝ)*
        v (e.symm (z,M.update t (e i).2 (e i).1 c z)) := by
  change (∑ j : Fin m, ((augmentedMatrix sys M e t c).entry i j : ℝ)*v j)=_
  calc
    (∑ j : Fin m, ((augmentedMatrix sys M e t c).entry i j : ℝ)*v j)=
        ∑ p : Fin n × S, (if p.2=M.update t (e i).2 (e i).1 c p.1
          then ((sys.matrix c).entry (e i).1 p.1 : ℝ) else 0)*v (e.symm p) := by
      apply Fintype.sum_equiv e
      intro j
      simp only [augmentedMatrix, e.symm_apply_apply]
      split_ifs <;> simp
    _ = _ := by simp [Fintype.sum_prod_type,ite_mul]

def monitorConsistent (M : FiniteMonitor.Monitor C n S) (e : Fin m ≃ Fin n × S) :
    (t : ℕ) → History C m t → Prop
  | 0,.initial i => (e i).2=M.initial (e i).1
  | t+1,.snoc h c j => monitorConsistent M e t h ∧
      (e j).2=M.update t (e (last t h)).2 (e (last t h)).1 c (e j).1

instance monitorConsistent_decidable (M : FiniteMonitor.Monitor C n S)
    (e : Fin m ≃ Fin n × S) (t : ℕ) (h : History C m t) : Decidable (monitorConsistent M e t h) := by
  induction h with
  | initial i => unfold monitorConsistent; infer_instance
  | @snoc t h c j ih =>
      change Decidable (monitorConsistent M e t h ∧
        (e j).2=M.update t (e (last t h)).2 (e (last t h)).1 c (e j).1)
      letI := ih
      infer_instance

theorem nextRow_consistent_expect (sys : FiniteControlSystem C n) (M : FiniteMonitor.Monitor C n S)
    (e : Fin m ≃ Fin n × S) (σ : BehavioralPolicy (monitorSystem sys M e))
    (t : ℕ) (h : History C m t) :
    (nextRow (monitorSystem sys M e) σ t h).expect
      (fun h' => if monitorConsistent M e (t+1) h' then 1 else 0)=
      if monitorConsistent M e t h then 1 else 0 := by
  rw [nextRow_expect]
  by_cases hh : monitorConsistent M e t h
  · simp only [monitorConsistent,hh,true_and,ite_true]
    have hv (c : C) : (matrixRow (monitorSystem sys M e) t (last t h) c).expect
        (fun j => if (e j).2=M.update t (e (last t h)).2 (e (last t h)).1 c (e j).1
          then 1 else 0)=1 := by
      rw [monitor_row_expect]
      simp only [e.apply_symm_apply,ite_true,mul_one]
      exact_mod_cast (sys.matrix c).row_sum_one (e (last t h)).1
    simp_rw [hv]
    exact Row.expect_const _ 1
  · simp [monitorConsistent,hh]

def monitorInitial (M : FiniteMonitor.Monitor C n S) (e : Fin m ≃ Fin n × S)
    (y : Fin n) : Row (Fin m) := Row.pure (e.symm (y,M.initial y))

theorem historyLaw_consistent_expect (sys : FiniteControlSystem C n) (M : FiniteMonitor.Monitor C n S)
    (e : Fin m ≃ Fin n × S) (σ : BehavioralPolicy (monitorSystem sys M e))
    (y : Fin n) (N : ℕ) :
    (historyLaw (monitorSystem sys M e) σ (monitorInitial M e y) N).expect
      (fun h => if monitorConsistent M e N h then 1 else 0)=1 := by
  induction N with
  | zero => simp [historyLaw,Row.expect_map,monitorInitial,monitorConsistent]
  | succ N ih =>
      rw [historyLaw,Row.expect_bind]
      simp_rw [nextRow_consistent_expect]
      exact ih

theorem actual_monitor_consistent (sys : FiniteControlSystem C n) (M : FiniteMonitor.Monitor C n S)
    (e : Fin m ≃ Fin n × S) (σ : BehavioralPolicy (monitorSystem sys M e))
    (y : Fin n) (N : ℕ) :
    ∀ᵐ h ∂actualHistoryMeasure (monitorSystem sys M e) σ (monitorInitial M e y) N,
      monitorConsistent M e N h := by
  have hm : actualHistoryMeasure (monitorSystem sys M e) σ (monitorInitial M e y) N
      {h | monitorConsistent M e N h}=1 := by
    rw [actualHistoryMeasure,row_event_probability,historyLaw_consistent_expect]
    simp
  rw [ae_iff]
  change actualHistoryMeasure (monitorSystem sys M e) σ (monitorInitial M e y) N
    ({h | monitorConsistent M e N h}ᶜ)=0
  rw [measure_compl (.of_discrete) (measure_ne_top _ _),hm,measure_univ]
  simp

def physicalTrace (e : Fin m ≃ Fin n × S) : (t : ℕ) → History C m t → FiniteMonitor.TraceHistory C n
  | 0,.initial i => ((e i).1,[])
  | t+1,.snoc h c j => FiniteMonitor.appendTrace (physicalTrace e t h) c (e j).1

theorem physicalTrace_length (e : Fin m ≃ Fin n × S) (t : ℕ) (h : History C m t) :
    (physicalTrace e t h).2.length=t := by
  induction h with
  | initial i => rfl
  | snoc h c j ih => simp [physicalTrace,FiniteMonitor.appendTrace,ih]

/-- The stored augmented state equals the literal original monitor run on
the recorded physical/control word, on every consistent history. -/
theorem consistent_eq_literal_run (M : FiniteMonitor.Monitor C n S)
    (e : Fin m ≃ Fin n × S) (t : ℕ) (h : History C m t) (hh : monitorConsistent M e t h) :
    e (last t h)=FiniteMonitor.run M 0 (physicalTrace e t h).1
      (M.initial (physicalTrace e t h).1) (physicalTrace e t h).2 := by
  induction h with
  | initial i => exact Prod.ext rfl hh
  | @snoc t h c j ih =>
      have hp := ih hh.1
      change e j=FiniteMonitor.run M 0 (physicalTrace e t h).1
        (M.initial (physicalTrace e t h).1) ((physicalTrace e t h).2++[(c,(e j).1)])
      rw [FiniteMonitor.run_append,← hp,physicalTrace_length,zero_add]
      exact Prod.ext rfl hh.2

theorem actual_monitor_literal_integral (sys : FiniteControlSystem C n)
    (M : FiniteMonitor.Monitor C n S) (e : Fin m ≃ Fin n × S)
    (σ : BehavioralPolicy (monitorSystem sys M e)) (y : Fin n) (N : ℕ) (F : Fin n × S → ℝ) :
    (∫ h, F (e (last N h)) ∂actualHistoryMeasure (monitorSystem sys M e) σ (monitorInitial M e y) N)=
    ∫ h, F (FiniteMonitor.run M 0 (physicalTrace e N h).1
      (M.initial (physicalTrace e N h).1) (physicalTrace e N h).2)
      ∂actualHistoryMeasure (monitorSystem sys M e) σ (monitorInitial M e y) N := by
  apply integral_congr_ae
  filter_upwards [actual_monitor_consistent sys M e σ y N] with h hh
  exact congrArg F (consistent_eq_literal_run M e N h hh)

end
end PermanssonResearch.ReverseSolver.Occupancy
