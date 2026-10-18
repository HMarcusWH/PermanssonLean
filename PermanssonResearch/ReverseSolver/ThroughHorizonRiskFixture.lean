import PermanssonResearch.ReverseSolver.ThroughHorizonRiskMonitor

/-! Exact regressions distinguish danger before success, danger after success,
and failure without danger. All updates operate on the unchanged physical word. -/

namespace PermanssonResearch.ReverseSolver.ThroughHorizonRisk
open FiniteMonitor

def fixtureSuccess : Monitor Unit 2 (AvoidState 0) :=
  (avoidResidenceMonitor (fun z : Fin 2 => z=0) (fun z : Fin 2 => z=1) 0).toMonitor

def fixtureMonitor := withRisk fixtureSuccess (fun z : Fin 2 => z=1)

theorem danger_at_zero_counts :
    (run fixtureMonitor 0 1 (fixtureMonitor.initial 1) []).2.2=true ∧
    (run fixtureMonitor 0 1 (fixtureMonitor.initial 1) []).2.1.1.2=false := by decide

theorem danger_after_completed_success_counts :
    (run fixtureMonitor 0 0 (fixtureMonitor.initial 0) [((),1)]).2.1.1.2=true ∧
    (run fixtureMonitor 0 0 (fixtureMonitor.initial 0) [((),1)]).2.2=true ∧
    fixtureMonitor.reward (run fixtureMonitor 0 0 (fixtureMonitor.initial 0) [((),1)]).1
      (run fixtureMonitor 0 0 (fixtureMonitor.initial 0) [((),1)]).2=1 := by decide

theorem simultaneous_target_danger_counts :
    let M : Monitor Unit 2 (AvoidState 0) :=
      (avoidResidenceMonitor (fun z : Fin 2 => z=0) (fun z : Fin 2 => z=0) 0).toMonitor
    let Q := withRisk M (fun z : Fin 2 => z=0)
    (run Q 0 0 (Q.initial 0) []).2.1.1.2=false ∧
      (run Q 0 0 (Q.initial 0) []).2.2=true := by decide

theorem failure_and_danger_are_not_complements :
    let M : Monitor Unit 2 (AvoidState 1) :=
      (avoidResidenceMonitor (fun z : Fin 2 => z=0) (fun _ : Fin 2 => False) 1).toMonitor
    let Q := withRisk M (fun _ : Fin 2 => False)
    (run Q 0 1 (Q.initial 1) [((),1)]).2.1.1.2=false ∧
      (run Q 0 1 (Q.initial 1) [((),1)]).2.2=false := by decide

end PermanssonResearch.ReverseSolver.ThroughHorizonRisk
