import PermanssonResearch.ReverseSolver.FiniteOccupancyMonitor
import PermanssonResearch.ReverseSolver.ResidenceSpecializationOptimality

/-! A separate ever-danger flag is appended to any finite monitor. Its update
continues after the original monitor has succeeded or failed. The terminal
flag is the literal through-horizon danger event under the actual normalized
history law, and is simultaneously a terminal occupancy score. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.ReverseSolver.ThroughHorizonRisk

open ControlledKernel FiniteMonitor
noncomputable section
variable {C S : Type*} [DecidableEq C] [Fintype C] {n : ℕ}

def dangerTest (D : Fin n → Prop) [DecidablePred D] (xs : List (Fin n)) : Bool :=
  xs.any (fun z => decide (D z))

theorem dangerTest_iff (D : Fin n → Prop) [DecidablePred D] (xs : List (Fin n)) :
    dangerTest D xs = true ↔ ∃ z ∈ xs, D z := by
  simp [dangerTest, List.any_eq_true]

/-- The success monitor is retained, and the separate risk flag always reads
the new physical observation. The physical transition row is untouched. -/
def withRisk (M : Monitor C n S) (D : Fin n → Prop) [DecidablePred D] :
    Monitor C n (S × Bool) where
  initial y := (M.initial y, decide (D y))
  update t q y c z := (M.update t q.1 y c z, q.2 || decide (D z))
  reward y q := M.reward y q.1

theorem run_withRisk (M : Monitor C n S) (D : Fin n → Prop) [DecidablePred D]
    (t : ℕ) (y : Fin n) (s : S) (b : Bool) (xs : List (C × Fin n)) :
    run (withRisk M D) t y (s,b) xs =
      ((run M t y s xs).1, ((run M t y s xs).2, b || dangerTest D (xs.map Prod.snd))) := by
  induction xs generalizing t y s b with
  | nil => simp [run, dangerTest]
  | cons a xs ih =>
      rcases a with ⟨c,z⟩
      simpa only [run, withRisk, List.map_cons, dangerTest, List.any_cons,
        Bool.or_assoc] using ih (t+1) z (M.update t s y c z) (b || decide (D z))

theorem initial_risk_iff_literal (M : Monitor C n S) (D : Fin n → Prop)
    [DecidablePred D] (y : Fin n) (xs : List (C × Fin n)) :
    (run (withRisk M D) 0 y ((withRisk M D).initial y) xs).2.2 = true ↔
      ∃ z ∈ y :: xs.map Prod.snd, D z := by
  rw [show (withRisk M D).initial y = (M.initial y, decide (D y)) from rfl,
    run_withRisk]
  change (decide (D y) || dangerTest D (xs.map Prod.snd)) = true ↔ _
  rw [Bool.or_eq_true,decide_eq_true_eq,dangerTest_iff]
  constructor
  · rintro (hy | ⟨z,hz,hd⟩)
    · exact ⟨y,by simp,hy⟩
    · exact ⟨z,List.mem_cons_of_mem y hz,hd⟩
  · rintro ⟨z,hz,hd⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact Or.inl hd
    · exact Or.inr ⟨z,hz,hd⟩

/-- On a word with N transitions, danger is seen exactly at an observation
index at most N, including observation zero. -/
theorem initial_risk_iff_time (M : Monitor C n S) (D : Fin n → Prop)
    [DecidablePred D] (N : ℕ) (y : Fin n) (xs : List (C × Fin n))
    (hlen : xs.length = N) :
    (run (withRisk M D) 0 y ((withRisk M D).initial y) xs).2.2 = true ↔
      ∃ (t : ℕ) (ht : t < (y :: xs.map Prod.snd).length),
        t ≤ N ∧ D (y :: xs.map Prod.snd)[t] := by
  rw [initial_risk_iff_literal, List.exists_mem_iff_getElem]
  constructor
  · rintro ⟨t,ht,hd⟩
    refine ⟨t,ht,?_,hd⟩
    simp only [List.length_cons,List.length_map,hlen] at ht
    omega
  · rintro ⟨t,ht,_,hd⟩
    exact ⟨t,ht,hd⟩

theorem original_reward_preserved (M : Monitor C n S) (D : Fin n → Prop)
    [DecidablePred D] (t : ℕ) (y : Fin n) (s : S) (b : Bool)
    (xs : List (C × Fin n)) :
    (withRisk M D).reward (run (withRisk M D) t y (s,b) xs).1
      (run (withRisk M D) t y (s,b) xs).2 =
        M.reward (run M t y s xs).1 (run M t y s xs).2 := by
  change M.reward (run (withRisk M D) t y (s,b) xs).1
    (run (withRisk M D) t y (s,b) xs).2.1 = _
  rw [run_withRisk]

variable [Fintype S] [DecidableEq S] {m : ℕ}

def riskScore (e : Fin m ≃ Fin n × (S × Bool)) (j : Fin m) : ℚ :=
  if (e j).2.2 then 1 else 0

def successScore (M : Monitor C n S) (e : Fin m ≃ Fin n × (S × Bool)) (j : Fin m) : ℚ :=
  M.reward (e j).1 (e j).2.1

theorem riskScore_bounds (e : Fin m ≃ Fin n × (S × Bool)) (j : Fin m) :
    0 ≤ riskScore e j ∧ riskScore e j ≤ 1 := by
  unfold riskScore
  split_ifs <;> norm_num

/-- The same augmented history stores both the original success objective
and an ever-danger flag; the latter is a genuine LP terminal score. -/
theorem actual_risk_integral_eq_literal (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (D : Fin n → Prop) [DecidablePred D]
    (e : Fin m ≃ Fin n × (S × Bool))
    (σ : Occupancy.BehavioralPolicy (Occupancy.monitorSystem sys (withRisk M D) e))
    (y : Fin n) (N : ℕ) :
    (∫ h, (riskScore e (Occupancy.last N h) : ℝ)
      ∂Occupancy.actualHistoryMeasure (Occupancy.monitorSystem sys (withRisk M D) e) σ
        (Occupancy.monitorInitial (withRisk M D) e y) N) =
      ∫ h, (if ∃ z ∈ (Occupancy.physicalTrace e N h).1 ::
        (Occupancy.physicalTrace e N h).2.map Prod.snd, D z then (1 : ℝ) else 0)
      ∂Occupancy.actualHistoryMeasure (Occupancy.monitorSystem sys (withRisk M D) e) σ
        (Occupancy.monitorInitial (withRisk M D) e y) N := by
  classical
  rw [show (fun h => (riskScore e (Occupancy.last N h) : ℝ)) =
    (fun h => if (e (Occupancy.last N h)).2.2 then (1:ℝ) else 0) by
      funext h; dsimp [riskScore]; split_ifs <;> norm_num]
  rw [Occupancy.actual_monitor_literal_integral sys (withRisk M D) e σ y N
    (fun q => if q.2.2 then (1:ℝ) else 0)]
  apply integral_congr_ae
  exact ae_of_all _ (fun h => by
    dsimp only
    have hh := initial_risk_iff_literal M D (Occupancy.physicalTrace e N h).1
      (Occupancy.physicalTrace e N h).2
    by_cases hd : ∃ z ∈ (Occupancy.physicalTrace e N h).1 ::
        (Occupancy.physicalTrace e N h).2.map Prod.snd, D z
    · rw [if_pos (hh.mpr hd),if_pos hd]
    · have hb : (run (withRisk M D) 0 (Occupancy.physicalTrace e N h).1
        ((withRisk M D).initial (Occupancy.physicalTrace e N h).1)
          (Occupancy.physicalTrace e N h).2).2.2 = false := Bool.eq_false_iff.mpr
            (fun ht => hd (hh.mp ht))
      rw [hb,if_neg (by decide : ¬false = true),if_neg hd])

theorem actual_risk_integral_eq_occupancy (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (D : Fin n → Prop) [DecidablePred D]
    (e : Fin m ≃ Fin n × (S × Bool))
    (σ : Occupancy.BehavioralPolicy (Occupancy.monitorSystem sys (withRisk M D) e))
    (y : Fin n) (N : ℕ) :
    (∫ h, (riskScore e (Occupancy.last N h) : ℝ)
      ∂Occupancy.actualHistoryMeasure (Occupancy.monitorSystem sys (withRisk M D) e) σ
        (Occupancy.monitorInitial (withRisk M D) e y) N) =
      ∑ j : Fin m, (riskScore e j : ℝ) *
        (Occupancy.occupancies (Occupancy.monitorSystem sys (withRisk M D) e) σ
          (Occupancy.monitorInitial (withRisk M D) e y) N).state (Fin.last N) j :=
  by
    simpa only [mul_comm] using Occupancy.actual_terminal_integral_eq_occupancy
      (Occupancy.monitorSystem sys (withRisk M D) e) σ
      (Occupancy.monitorInitial (withRisk M D) e y) N (fun j => (riskScore e j : ℝ))

/-- The literal danger-event probability is the hard-risk linear functional
of actual terminal state masses, for every real full-history controller. -/
theorem actual_risk_probability_eq_occupancy (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (D : Fin n → Prop) [DecidablePred D]
    (e : Fin m ≃ Fin n × (S × Bool))
    (σ : Occupancy.BehavioralPolicy (Occupancy.monitorSystem sys (withRisk M D) e))
    (y : Fin n) (N : ℕ) :
    Occupancy.actualHistoryMeasure (Occupancy.monitorSystem sys (withRisk M D) e) σ
      (Occupancy.monitorInitial (withRisk M D) e y) N
      {h | ∃ z ∈ (Occupancy.physicalTrace e N h).1 ::
        (Occupancy.physicalTrace e N h).2.map Prod.snd, D z} =
      ENNReal.ofReal (∑ j : Fin m, (riskScore e j : ℝ) *
        (Occupancy.occupancies (Occupancy.monitorSystem sys (withRisk M D) e) σ
          (Occupancy.monitorInitial (withRisk M D) e y) N).state (Fin.last N) j) := by
  classical
  have hp := Occupancy.row_event_probability
    (Occupancy.historyLaw (Occupancy.monitorSystem sys (withRisk M D) e) σ
      (Occupancy.monitorInitial (withRisk M D) e y) N)
    (fun h => ∃ z ∈ (Occupancy.physicalTrace e N h).1 ::
      (Occupancy.physicalTrace e N h).2.map Prod.snd, D z)
  rw [ActionTrace.Row.expect_eq_integral] at hp
  calc
    _ = ENNReal.ofReal (∫ h, (if ∃ z ∈ (Occupancy.physicalTrace e N h).1 ::
        (Occupancy.physicalTrace e N h).2.map Prod.snd, D z then (1:ℝ) else 0)
      ∂Occupancy.actualHistoryMeasure (Occupancy.monitorSystem sys (withRisk M D) e) σ
        (Occupancy.monitorInitial (withRisk M D) e y) N) := hp
    _ = _ := congrArg ENNReal.ofReal
      ((actual_risk_integral_eq_literal sys M D e σ y N).symm.trans
        (actual_risk_integral_eq_occupancy sys M D e σ y N))

/-- Appending risk preserves the original terminal objective under that same
actual normalized law, so the two scores can be constrained simultaneously. -/
theorem actual_success_integral_eq_original (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (D : Fin n → Prop) [DecidablePred D]
    (e : Fin m ≃ Fin n × (S × Bool))
    (σ : Occupancy.BehavioralPolicy (Occupancy.monitorSystem sys (withRisk M D) e))
    (y : Fin n) (N : ℕ) :
    (∫ h, (successScore M e (Occupancy.last N h) : ℝ)
      ∂Occupancy.actualHistoryMeasure (Occupancy.monitorSystem sys (withRisk M D) e) σ
        (Occupancy.monitorInitial (withRisk M D) e y) N) =
      ∫ h, (M.reward
        (run M 0 (Occupancy.physicalTrace e N h).1
          (M.initial (Occupancy.physicalTrace e N h).1) (Occupancy.physicalTrace e N h).2).1
        (run M 0 (Occupancy.physicalTrace e N h).1
          (M.initial (Occupancy.physicalTrace e N h).1) (Occupancy.physicalTrace e N h).2).2 : ℝ)
      ∂Occupancy.actualHistoryMeasure (Occupancy.monitorSystem sys (withRisk M D) e) σ
        (Occupancy.monitorInitial (withRisk M D) e y) N := by
  rw [show (fun h => (successScore M e (Occupancy.last N h) : ℝ)) =
    (fun h => (M.reward (e (Occupancy.last N h)).1 (e (Occupancy.last N h)).2.1 : ℝ))
      from rfl]
  rw [Occupancy.actual_monitor_literal_integral sys (withRisk M D) e σ y N
    (fun q => (M.reward q.1 q.2.1 : ℝ))]
  apply integral_congr_ae
  exact ae_of_all _ (fun h => by
    change (M.reward
      (run (withRisk M D) 0 (Occupancy.physicalTrace e N h).1
        (M.initial (Occupancy.physicalTrace e N h).1,
          decide (D (Occupancy.physicalTrace e N h).1)) (Occupancy.physicalTrace e N h).2).1
      (run (withRisk M D) 0 (Occupancy.physicalTrace e N h).1
        (M.initial (Occupancy.physicalTrace e N h).1,
          decide (D (Occupancy.physicalTrace e N h).1)) (Occupancy.physicalTrace e N h).2).2.1 : ℝ) = _
    rw [run_withRisk])

end
end PermanssonResearch.ReverseSolver.ThroughHorizonRisk
