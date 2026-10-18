import PermanssonResearch.ReverseSolver.FlowPolicyOptimality
import PermanssonResearch.ReverseSolver.PolytopeRegression

namespace PermanssonResearch.ReverseSolver.Occupancy.RiskWitness

open ActionTrace ControlledKernel MeasureTheory ExactPolytope

noncomputable section

def transition (c : Bool) : RationalMarkovMatrix 3 where
  entry y z := if y = 0 then
    if c then ![0,9/10,1/10] z else ![1/5,4/5,0] z
    else if z = y then 1 else 0
  entry_nonneg y z := by fin_cases y <;> fin_cases z <;> cases c <;> norm_num
  row_sum_one y := by fin_cases y <;> cases c <;> norm_num [Fin.sum_univ_succ]

def system : TimeSystem Bool 3 where
  states_nonempty := by norm_num
  options _ _ := Finset.univ
  options_nonempty _ _ := ⟨false, Finset.mem_univ _⟩
  matrix _ c := transition c

def initial : Row (Fin 3) := Row.pure 0
def reward : Fin 3 → ℚ := ![0,1,0]
def danger : Fin 3 → ℚ := ![0,0,1]

theorem one_step_actual (σ : BehavioralPolicy system) (R : Fin 3 → ℝ) :
    actualTerminalScore system σ initial 1 R =
      (σ.control 0 (History.initial 0)).expect
        (fun c => (matrixRow system 0 0 c).expect R) := by
  unfold actualTerminalScore actualHistoryMeasure
  rw [← Row.expect_eq_integral, historyLaw_step_expect, historyLaw, Row.expect_map]
  simp only [initial, Row.expect_pure, last]

theorem actual_success_formula (σ : BehavioralPolicy system) :
    actualTerminalScore system σ initial 1 (fun y => (reward y : ℝ)) =
      4/5 + (σ.control 0 (History.initial 0)).mass true / 10 := by
  rw [one_step_actual]
  have ht := (σ.control 0 (History.initial 0)).total
  simp at ht
  simp [Row.expect, matrixRow, system, transition, reward, Fin.sum_univ_succ]
  linarith

theorem actual_danger_formula (σ : BehavioralPolicy system) :
    actualTerminalScore system σ initial 1 (fun y => (danger y : ℝ)) =
      (σ.control 0 (History.initial 0)).mass true / 10 := by
  rw [one_step_actual]
  simp [Row.expect, matrixRow, system, transition, danger, Fin.sum_univ_succ]
  ring

def coinRow (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : Row Bool where
  mass c := if c then p else 1-p
  nonneg c := by
    cases c
    · exact sub_nonneg.mpr hp1
    · exact hp
  total := by simp

def policy (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : BehavioralPolicy system where
  control _ _ := coinRow p hp hp1
  supported _ _ c hc := False.elim (hc (Finset.mem_univ c))

theorem actual_half_attains :
    actualTerminalScore system (policy (1/2) (by norm_num) (by norm_num)) initial 1
      (fun y => (reward y : ℝ)) = 17/20 ∧
    actualTerminalScore system (policy (1/2) (by norm_num) (by norm_num)) initial 1
      (fun y => (danger y : ℝ)) = 1/20 := by
  rw [actual_success_formula, actual_danger_formula]
  norm_num [policy, coinRow]

theorem all_actual_feasible_success_le (σ : BehavioralPolicy system)
    (hr : actualTerminalScore system σ initial 1 (fun y => (danger y : ℝ)) ≤ 1/20) :
    actualTerminalScore system σ initial 1 (fun y => (reward y : ℝ)) ≤ 17/20 := by
  rw [actual_success_formula]
  rw [actual_danger_formula] at hr
  linarith

theorem full_risky_choice_is_infeasible (σ : BehavioralPolicy system)
    (hc : (σ.control 0 (History.initial 0)).mass true = 1) :
    1/20 < actualTerminalScore system σ initial 1 (fun y => (danger y : ℝ)) := by
  rw [actual_danger_formula, hc]
  norm_num

end
end PermanssonResearch.ReverseSolver.Occupancy.RiskWitness
