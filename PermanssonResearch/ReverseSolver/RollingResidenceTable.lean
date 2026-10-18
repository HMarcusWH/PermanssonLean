import PermanssonResearch.ReverseSolver.RollingMonitorTable
import PermanssonResearch.ReverseSolver.MonitorEventOptimality
import Mathlib.Logic.Equiv.Fin.Basic

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open ControlledKernel

def residenceEnumeration (m : ℕ) : Fin ((m+2)*2) ≃ ResidenceState m :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finTwoEquiv)

variable {C : Type*} [DecidableEq C] [Fintype C] {n : ℕ}

def rollingResidenceValue (sys : FiniteControlSystem C n)
    (G : Fin n → Prop) [DecidablePred G] (m T : ℕ) (y : Fin n) : ℚ :=
  tableRead (residenceEnumeration m)
    (rollingMonitorTable sys (compactResidenceMonitor G m).toMonitor
      (residenceEnumeration m) (T+m) 0) y ((compactResidenceMonitor G m).initial y)

/-- The actual array-backed table value is the optimum of the literal
entry-by-deadline residence event under every real behavioral history policy.
It uses exactly `n` rows and `2*(m+2)` summary columns per backwards layer. -/
theorem rollingResidence_optimal_and_attained (sys : FiniteControlSystem C n)
    (G : Fin n → Prop) [DecidablePred G] (m T : ℕ) (y : Fin n) :
    (∀ σ : BehavioralPolicy sys, behavioralResidenceProbability sys σ G m T y≤
      (rollingResidenceValue sys G m T y : ℝ)) ∧
    (∃ σ : BehavioralPolicy sys, behavioralResidenceProbability sys σ G m T y=
      (rollingResidenceValue sys G m T y : ℝ)) := by
  simpa only [rollingResidenceValue,rollingMonitorTable_eq_value] using
    behavioralResidence_optimal_and_attained sys G m T y

end PermanssonResearch.ReverseSolver.FiniteMonitor
