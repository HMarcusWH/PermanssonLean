import PermanssonResearch.ReverseSolver.MonitorOptimality
import PermanssonResearch.ReverseSolver.CompactResidenceMonitor
import PermanssonResearch.ReverseSolver.ChronologicalFiniteLaw

/-!
# Literal residence probability under real behavioral histories

The objective below is specified directly on physical observation words. Its
chronological product-law probability is proved equal to the compact monitor
expectation before invoking Bellman optimality.
-/

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open ControlledKernel

universe uC uS

variable {C : Type uC} [DecidableEq C] [Fintype C] {n : ℕ} {S : Type uS}

def observationRun (M : ObservationMonitor n S) : ℕ → S → List (Fin n) → S
  | _, s, [] => s
  | t, s, z::xs => observationRun M (t+1) (M.update t s z) xs

theorem run_observation_second (M : ObservationMonitor n S) (t : ℕ)
    (y : Fin n) (s : S) (xs : List (C × Fin n)) :
    (run M.toMonitor t y s xs).2 = observationRun M t s (xs.map Prod.snd) := by
  induction xs generalizing t y s with
  | nil => rfl
  | cons a xs ih => exact ih _ _ _

theorem observationRun_residence (G : Fin n → Prop) [DecidablePred G]
    (m t : ℕ) (q : ResidenceState m) (xs : List (Fin n)) :
    observationRun (compactResidenceMonitor G m) t q xs = xs.foldl (residenceStep G m) q := by
  induction xs generalizing t q with
  | nil => rfl
  | cons z xs ih => exact ih _ _

/-- Probability of the literal retryable block event under the normalized
chronological state/control product law. -/
noncomputable def behavioralResidenceProbability (sys : FiniteControlSystem C n)
    (σ : BehavioralPolicy sys) (G : Fin n → Prop) [DecidablePred G]
    (m T : ℕ) (y : Fin n) : ℝ :=
  ((traceWords C n (T+m)).map (fun xs => traceMass sys σ 0 (y,[]) y xs *
    if Residence.hasRun G (m+1) (y :: xs.map Prod.snd) then 1 else 0)).sum

theorem trace_residence_success_iff_entry (G : Fin n → Prop) [DecidablePred G]
    (m T : ℕ) (y : Fin n) (xs : List (C × Fin n))
    (hx : xs ∈ traceWords C n (T+m)) :
    Residence.hasRun G (m+1) (y::xs.map Prod.snd)=true ↔
      ∃ pre block post, y::xs.map Prod.snd=pre++block++post ∧
        pre.length≤T ∧ block.length=m+1 ∧ ∀ z ∈ block, G z := by
  rw [Residence.hasRun_iff_block]
  constructor
  · rintro ⟨pre, block, post, he, hl, ha⟩
    have hw := congrArg List.length he
    have hxlen := traceWords_length (T+m) xs hx
    simp only [List.length_cons, List.length_map, List.length_append, hl, hxlen] at hw
    exact ⟨pre, block, post, he, by omega, hl, ha⟩
  · rintro ⟨pre, block, post, he, _, hl, ha⟩
    exact ⟨pre, block, post, he, hl, ha⟩

theorem behavioralResidenceProbability_eq_monitor (sys : FiniteControlSystem C n)
    (σ : BehavioralPolicy sys) (G : Fin n → Prop) [DecidablePred G]
    (m T : ℕ) (y : Fin n) :
    behavioralResidenceProbability sys σ G m T y =
      traceExpectation sys (compactResidenceMonitor G m).toMonitor σ (T+m) 0
        (y,[]) y ((compactResidenceMonitor G m).initial y) := by
  unfold behavioralResidenceProbability traceExpectation
  apply congrArg List.sum
  apply List.map_congr_left
  intro xs _
  rw [run_observation_second, observationRun_residence]
  have hs : ((xs.map Prod.snd).foldl (residenceStep G m)
      ((compactResidenceMonitor G m).initial y)).2 =
        Residence.hasRun G (m+1) (y::xs.map Prod.snd) :=
    (residenceScan_invariant G m (y::xs.map Prod.snd)).2
  simp only [ObservationMonitor.toMonitor, compactResidenceMonitor] at hs ⊢
  simp only [hs]
  split_ifs <;> norm_num

/-- All nonanticipating behavioral full-history policies, with real mixing
probabilities, are bounded by the compact rational value, and one attains it. -/
theorem behavioralResidence_optimal_and_attained (sys : FiniteControlSystem C n)
    (G : Fin n → Prop) [DecidablePred G] (m T : ℕ) (y : Fin n) :
    (∀ σ : BehavioralPolicy sys, behavioralResidenceProbability sys σ G m T y ≤
      (value sys (compactResidenceMonitor G m).toMonitor (T+m) 0 y
        ((compactResidenceMonitor G m).initial y) : ℝ)) ∧
    (∃ σ : BehavioralPolicy sys, behavioralResidenceProbability sys σ G m T y =
      (value sys (compactResidenceMonitor G m).toMonitor (T+m) 0 y
        ((compactResidenceMonitor G m).initial y) : ℝ)) := by
  simpa only [behavioralResidenceProbability_eq_monitor, ObservationMonitor.toMonitor] using
    monitor_optimal_and_attained sys (compactResidenceMonitor G m).toMonitor (T+m) y

end PermanssonResearch.ReverseSolver.FiniteMonitor
