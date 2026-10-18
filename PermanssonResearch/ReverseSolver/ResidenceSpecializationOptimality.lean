import PermanssonResearch.ReverseSolver.MonitorEventOptimality
import PermanssonResearch.ReverseSolver.FirstEntryMonitor
import PermanssonResearch.ReverseSolver.AvoidResidenceMonitor
import PermanssonResearch.ReverseSolver.AvoidResidenceHistoryBridge

/-!
# Exact first-entry and before-danger behavioral-history optimization

The two literal word predicates are specified before the compact monitor is
used. Real behavioral histories may remember all prior realized actions.
-/

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open ControlledKernel

universe uC

variable {C : Type uC} [DecidableEq C] [Fintype C] {n : ℕ}

theorem observationRun_first (G : Fin n → Prop) [DecidablePred G]
    (T m t : ℕ) (q : FirstState m) (xs : List (Fin n)) :
    observationRun (firstEntryMonitor G T m) t q xs = firstRun G T m (t+1) q xs := by
  induction xs generalizing t q with
  | nil => rfl
  | cons z xs ih => exact ih _ _

theorem observationRun_avoid (G D : Fin n → Prop) [DecidablePred G] [DecidablePred D]
    (m t : ℕ) (q : AvoidState m) (xs : List (Fin n)) :
    observationRun (avoidResidenceMonitor G D m) t q xs = avoidRun G D m q xs := by
  induction xs generalizing t q with
  | nil => rfl
  | cons z xs ih => exact ih _ _

noncomputable def behavioralFirstEntryProbability (sys : FiniteControlSystem C n)
    (σ : BehavioralPolicy sys) (G : Fin n → Prop) [DecidablePred G]
    (m T : ℕ) (y : Fin n) : ℝ :=
  ((traceWords C n (T+m)).map (fun xs => traceMass sys σ 0 (y,[]) y xs *
    if firstEntryTest G T (m+1) 0 (y::xs.map Prod.snd) then 1 else 0)).sum

theorem behavioralFirstEntryProbability_eq_monitor (sys : FiniteControlSystem C n)
    (σ : BehavioralPolicy sys) (G : Fin n → Prop) [DecidablePred G]
    (m T : ℕ) (y : Fin n) :
    behavioralFirstEntryProbability sys σ G m T y =
      traceExpectation sys (firstEntryMonitor G T m).toMonitor σ (T+m) 0
        (y,[]) y ((firstEntryMonitor G T m).initial y) := by
  unfold behavioralFirstEntryProbability traceExpectation
  apply congrArg List.sum
  apply List.map_congr_left
  intro xs _
  rw [run_observation_second, observationRun_first]
  simp only [ObservationMonitor.toMonitor, firstEntryMonitor]
  have hh := firstRun_correct G T m 0 .waiting (y::xs.map Prod.snd)
  simp only [firstRun, firstCompletion, firstEntryMonitor] at hh
  split_ifs <;> simp_all

theorem behavioralFirstEntry_optimal_and_attained (sys : FiniteControlSystem C n)
    (G : Fin n → Prop) [DecidablePred G] (m T : ℕ) (y : Fin n) :
    (∀ σ : BehavioralPolicy sys, behavioralFirstEntryProbability sys σ G m T y ≤
      (value sys (firstEntryMonitor G T m).toMonitor (T+m) 0 y
        ((firstEntryMonitor G T m).initial y) : ℝ)) ∧
    (∃ σ : BehavioralPolicy sys, behavioralFirstEntryProbability sys σ G m T y =
      (value sys (firstEntryMonitor G T m).toMonitor (T+m) 0 y
        ((firstEntryMonitor G T m).initial y) : ℝ)) := by
  simpa only [behavioralFirstEntryProbability_eq_monitor, ObservationMonitor.toMonitor] using
    monitor_optimal_and_attained sys (firstEntryMonitor G T m).toMonitor (T+m) y

noncomputable def behavioralAvoidResidenceProbability (sys : FiniteControlSystem C n)
    (σ : BehavioralPolicy sys) (G D : Fin n → Prop) [DecidablePred G] [DecidablePred D]
    (m T : ℕ) (y : Fin n) : ℝ :=
  ((traceWords C n (T+m)).map (fun xs => traceMass sys σ 0 (y,[]) y xs *
    if Residence.hasRun G (m+1) (safePrefix D (y::xs.map Prod.snd)) then 1 else 0)).sum

theorem trace_avoid_success_iff_entry (G D : Fin n → Prop)
    [DecidablePred G] [DecidablePred D] (m T : ℕ) (y : Fin n)
    (xs : List (C × Fin n)) (hx : xs ∈ traceWords C n (T+m)) :
    Residence.hasRun G (m+1) (safePrefix D (y::xs.map Prod.snd))=true ↔
      ∃ pre block post, y::xs.map Prod.snd=pre++block++post ∧
        pre.length≤T ∧ block.length=m+1 ∧ (∀ z ∈ block, G z) ∧
          ∀ z ∈ pre++block, ¬D z := by
  rw [safePrefix_hasRun_iff_block]
  constructor
  · rintro ⟨pre,block,post,he,hl,hg,hs⟩
    have hh := congrArg List.length he
    have hlen := traceWords_length (T+m) xs hx
    simp only [List.length_cons, List.length_map, List.length_append, hlen, hl] at hh
    exact ⟨pre,block,post,he,by omega,hl,hg,hs⟩
  · rintro ⟨pre,block,post,he,_,hl,hg,hs⟩
    exact ⟨pre,block,post,he,hl,hg,hs⟩

theorem behavioralAvoidResidenceProbability_eq_monitor (sys : FiniteControlSystem C n)
    (σ : BehavioralPolicy sys) (G D : Fin n → Prop) [DecidablePred G] [DecidablePred D]
    (m T : ℕ) (y : Fin n) :
    behavioralAvoidResidenceProbability sys σ G D m T y =
      traceExpectation sys (avoidResidenceMonitor G D m).toMonitor σ (T+m) 0
        (y,[]) y ((avoidResidenceMonitor G D m).initial y) := by
  unfold behavioralAvoidResidenceProbability traceExpectation
  apply congrArg List.sum
  apply List.map_congr_left
  intro xs _
  rw [run_observation_second, observationRun_avoid]
  simp only [ObservationMonitor.toMonitor, avoidResidenceMonitor]
  have hh := avoidRun_safePrefix G D m (0,false) (y::xs.map Prod.snd)
  change (avoidRun G D m ((0,false),false) (y::xs.map Prod.snd)).1.2 =
    (residenceScan G m (safePrefix D (y::xs.map Prod.snd))).2 at hh
  rw [(residenceScan_invariant G m _).2] at hh
  simp only [avoidRun, avoidResidenceMonitor] at hh
  simp only [hh]
  split_ifs <;> norm_num

theorem behavioralAvoidResidence_optimal_and_attained (sys : FiniteControlSystem C n)
    (G D : Fin n → Prop) [DecidablePred G] [DecidablePred D]
    (m T : ℕ) (y : Fin n) :
    (∀ σ : BehavioralPolicy sys, behavioralAvoidResidenceProbability sys σ G D m T y ≤
      (value sys (avoidResidenceMonitor G D m).toMonitor (T+m) 0 y
        ((avoidResidenceMonitor G D m).initial y) : ℝ)) ∧
    (∃ σ : BehavioralPolicy sys, behavioralAvoidResidenceProbability sys σ G D m T y =
      (value sys (avoidResidenceMonitor G D m).toMonitor (T+m) 0 y
        ((avoidResidenceMonitor G D m).initial y) : ℝ)) := by
  simpa only [behavioralAvoidResidenceProbability_eq_monitor, ObservationMonitor.toMonitor] using
    monitor_optimal_and_attained sys (avoidResidenceMonitor G D m).toMonitor (T+m) y

end PermanssonResearch.ReverseSolver.FiniteMonitor
