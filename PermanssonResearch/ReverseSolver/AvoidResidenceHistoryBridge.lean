import PermanssonResearch.ReverseSolver.AvoidResidenceMonitor

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open HistoryDependent ControlledKernel
open PermanssonLean.ProbabilitySupport

variable {Y : Type*} (G D : Y → Prop) [DecidablePred G] [DecidablePred D]

theorem avoidRun_append (m : ℕ) (q : AvoidState m) (xs ys : List Y) :
    avoidRun G D m q (xs++ys)=avoidRun G D m (avoidRun G D m q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons z xs ih => exact ih _

theorem avoidResidence_summary {n i : ℕ} (G D : Fin n → Prop)
    [DecidablePred G] [DecidablePred D] (m : ℕ) (h : History n i) :
    summary (avoidResidenceMonitor G D m) i h =
      avoidRun G D m ((0,false),false) (Residence.historyWord h) := by
  induction i with
  | zero =>
      simp [summary, avoidResidenceMonitor, Residence.historyWord, last,
        List.ofFn_zero, avoidRun]
  | succ i ih =>
      rw [summary, ih]
      have hw : Residence.historyWord h =
          Residence.historyWord (observedPrefix h i i.le_succ) ++ [last h] := by
        unfold Residence.historyWord
        rw [stepsFromHistory_snoc]
        rfl
      rw [hw, avoidRun_append]
      rfl

/-- The literal success-before-danger event; safe observations include time
zero and the entire successful block, while observations after it are free. -/
def beforeDangerResidenceEvent {n : ℕ} (G D : Fin n → Prop)
    (m T : ℕ) : Set (History n (T+m)) :=
  {h | ∃ pre block post, Residence.historyWord h=pre++block++post ∧
    pre.length≤T ∧ block.length=m+1 ∧ (∀ z ∈ block, G z) ∧
      ∀ z ∈ pre++block, ¬D z}

theorem avoidResidence_event_eq {n : ℕ} (G D : Fin n → Prop)
    [DecidablePred G] [DecidablePred D] (m T : ℕ) :
    monitorEvent (avoidResidenceMonitor G D m) (T+m)=beforeDangerResidenceEvent G D m T := by
  ext h
  change (summary (avoidResidenceMonitor G D m) (T+m) h).1.2=true ↔ _
  rw [avoidResidence_summary, avoidScan_success_iff_block]
  constructor
  · rintro ⟨pre, block, post, he, hl, hg, hs⟩
    have hh := congrArg List.length he
    simp only [Residence.historyWord_length, List.length_append, hl] at hh
    exact ⟨pre,block,post,he,by omega,hl,hg,hs⟩
  · rintro ⟨pre,block,post,he,_,hl,hg,hs⟩
    exact ⟨pre,block,post,he,hl,hg,hs⟩

theorem beforeDanger_history_probability_optimal_and_attained
    {C : Type*} [DecidableEq C] {n : ℕ} (sys : FiniteControlSystem C n)
    (G D : Fin n → Prop) [DecidablePred G] [DecidablePred D]
    (m T : ℕ) (x : Fin n) :
    (∀ σ : HistoryPolicy sys,
      prefixLaw sys σ (T+m) x (T+m) (beforeDangerResidenceEvent G D m T) ≤
        ENNReal.ofReal ((value sys (avoidResidenceMonitor G D m).toMonitor (T+m) 0 x
          ((avoidResidenceMonitor G D m).initial x) : ℚ) : ℝ)) ∧
    prefixLaw sys (monitorHistoryMaximizer sys (avoidResidenceMonitor G D m)) (T+m) x (T+m)
      (beforeDangerResidenceEvent G D m T) =
        ENNReal.ofReal ((value sys (avoidResidenceMonitor G D m).toMonitor (T+m) 0 x
          ((avoidResidenceMonitor G D m).initial x) : ℚ) : ℝ) := by
  simpa only [avoidResidence_event_eq] using
    monitor_history_probability_optimal_and_attained sys (avoidResidenceMonitor G D m) (T+m) x

end PermanssonResearch.ReverseSolver.FiniteMonitor
