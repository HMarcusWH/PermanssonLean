import PermanssonResearch.ReverseSolver.FiniteOccupancyMonitor
import PermanssonResearch.ReverseSolver.FiniteOccupancyReconstruction

/-! A separate actual monitor-law regression: a binding risk budget requires
mixing. The monitor remembers the realized control; the physical risky row
has danger probability one half. Zero-mass augmented states remain legal. -/

open MeasureTheory
namespace PermanssonResearch.ReverseSolver.Occupancy.RiskFixture
open ControlledKernel ActionTrace
noncomputable section

def physicalMatrix (c : Bool) : RationalMarkovMatrix 2 where
  entry _ z := if c then 1/2 else if z=0 then 1 else 0
  entry_nonneg _ z := by split_ifs <;> norm_num
  row_sum_one _ := by cases c <;> norm_num [Fin.sum_univ_two]

def physicalSystem : FiniteControlSystem Bool 2 where
  states_nonempty := by decide
  baseline := physicalMatrix false
  options _ := Finset.univ
  options_nonempty _ := ⟨false,Finset.mem_univ _⟩
  matrix := physicalMatrix

def monitor : FiniteMonitor.Monitor Bool 2 (Fin 2) where
  initial _ := 0
  update _ _ _ c _ := if c then 1 else 0
  reward _ s := if s=1 then 1 else 0

def enumeration : Fin 4 ≃ Fin 2 × Fin 2 := (finProdFinEquiv (m:=2) (n:=2)).symm
def system : TimeSystem Bool 4 := monitorSystem physicalSystem monitor enumeration
def initial : Row (Fin 4) := monitorInitial monitor enumeration 0

def constantPolicy (p : Row Bool) : BehavioralPolicy system where
  control _ _ := p
  supported _ _ c hc := by simpa [system,monitorSystem,physicalSystem] using hc

def success (i : Fin 4) : ℝ := if (enumeration i).2=1 then 1 else 0
def danger (i : Fin 4) : ℝ := if (enumeration i).1=1 then 1 else 0

theorem one_step_integral (p : Row Bool) (F : Fin 2 × Fin 2 → ℝ) :
    actualTerminalScore system (constantPolicy p) initial 1 (fun i => F (enumeration i))=
      p.expect (fun c => ∑ z : Fin 2, ((physicalMatrix c).entry 0 z : ℝ)*
        F (z,if c then 1 else 0)) := by
  unfold actualTerminalScore actualHistoryMeasure
  rw [← Row.expect_eq_integral,historyLaw_step_expect]
  simp only [historyLaw,Row.expect_map,initial,monitorInitial,Row.expect_pure,
    constantPolicy,last]
  rw [show system=monitorSystem physicalSystem monitor enumeration from rfl]
  congr 1
  funext c
  rw [monitor_row_expect]
  simp [monitor,physicalSystem]

theorem actual_success (p : Row Bool) :
    actualTerminalScore system (constantPolicy p) initial 1 success=p.mass true := by
  change actualTerminalScore system (constantPolicy p) initial 1
    (fun i => (fun q : Fin 2 × Fin 2 => if q.2=1 then (1:ℝ) else 0) (enumeration i))=_
  rw [one_step_integral p (fun q : Fin 2 × Fin 2 => if q.2=1 then (1:ℝ) else 0)]
  simp [Row.expect,Fintype.sum_bool,Fin.sum_univ_two,physicalMatrix]
  ring

theorem actual_danger (p : Row Bool) :
    actualTerminalScore system (constantPolicy p) initial 1 danger=p.mass true/2 := by
  change actualTerminalScore system (constantPolicy p) initial 1
    (fun i => (fun q : Fin 2 × Fin 2 => if q.1=1 then (1:ℝ) else 0) (enumeration i))=_
  rw [one_step_integral p (fun q : Fin 2 × Fin 2 => if q.1=1 then (1:ℝ) else 0)]
  simp [Row.expect,Fintype.sum_bool,Fin.sum_univ_two,physicalMatrix]
  ring

def halfRow : Row Bool where
  mass _ := 1/2
  nonneg _ := by norm_num
  total := by norm_num [Fintype.sum_bool]

theorem actual_mixing_risk_boundary :
    actualTerminalScore system (constantPolicy halfRow) initial 1 success=1/2 ∧
    actualTerminalScore system (constantPolicy halfRow) initial 1 danger=1/4 ∧
    1/4<actualTerminalScore system (constantPolicy (Row.pure true)) initial 1 danger ∧
    actualTerminalScore system (constantPolicy (Row.pure false)) initial 1 success<1/2 := by
  rw [actual_success,actual_danger,actual_danger,actual_success]
  norm_num [halfRow,Row.pure]

def mixingFlow : Flow system initial 1 := occupancies system (constantPolicy halfRow) initial 1

theorem reconstructed_mixing_scores :
    actualTerminalScore system mixingFlow.policy initial 1 success=1/2 ∧
    actualTerminalScore system mixingFlow.policy initial 1 danger=1/4 := by
  have hs : actualTerminalScore system mixingFlow.policy initial 1 success=
      actualTerminalScore system (constantPolicy halfRow) initial 1 success := by
    rw [actualTerminalScore,reconstructed_actual_terminal_integral]
    exact (actual_terminal_integral_eq_occupancy system (constantPolicy halfRow) initial 1 success).symm
  have hd : actualTerminalScore system mixingFlow.policy initial 1 danger=
      actualTerminalScore system (constantPolicy halfRow) initial 1 danger := by
    rw [actualTerminalScore,reconstructed_actual_terminal_integral]
    exact (actual_terminal_integral_eq_occupancy system (constantPolicy halfRow) initial 1 danger).symm
  exact ⟨hs.trans actual_mixing_risk_boundary.1,hd.trans actual_mixing_risk_boundary.2.1⟩

theorem zero_mass_initial_actions (j : Fin 4)
    (hj : j≠enumeration.symm (0,0)) :
    mixingFlow.state 0 j=0 ∧ ∀ c, mixingFlow.action 0 j c=0 := by
  have hd : mixingFlow.state 0 j=0 := by
    rw [mixingFlow.initial]
    simp [initial,monitorInitial,monitor,Row.pure,hj,Ne.symm hj]
  exact ⟨hd,fun c => mixingFlow.action_zero_of_state_zero 0 j hd c⟩

/-- Reconstruction is legal even at histories beginning in unreachable
augmented states; legality is not restricted to the realized support. -/
theorem reconstructed_policy_legal_every_history (t : ℕ) (h : History Bool 4 t) (c : Bool)
    (hc : c∉system.options t (last t h)) : (mixingFlow.policy.control t h).mass c=0 :=
  mixingFlow.policy.supported t h c hc

end
end PermanssonResearch.ReverseSolver.Occupancy.RiskFixture
