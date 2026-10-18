import PermanssonResearch.ReverseSolver.ChronologicalFiniteLaw
import PermanssonResearch.ReverseSolver.MonitorOptimality

namespace PermanssonResearch.ReverseSolver.FiniteMonitor

open ControlledKernel

universe uC uS

def FiniteProbabilityLaw.expectation {A : Type*} [DecidableEq A]
    (L : FiniteProbabilityLaw A) (f : A → ℝ) : ℝ := ∑ a ∈ L.support, L.atom a*f a

variable {C : Type uC} [DecidableEq C] [Fintype C] {n : ℕ} {S : Type uS}

/-- The independently normalized product-atom probability law has exactly the
monitor terminal expectation used in the optimization theorem. -/
theorem chronologicalLaw_monitor_expectation (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (σ : BehavioralPolicy sys) (r t : ℕ)
    (h : TraceHistory C n) (y : Fin n) (s : S) :
    (chronologicalLaw sys σ r t h y).expectation
      (fun xs => (M.reward (run M t y s xs).1 (run M t y s xs).2 : ℝ)) =
        traceExpectation sys M σ r t h y s := by
  unfold FiniteProbabilityLaw.expectation traceExpectation
  change (∑ xs ∈ (traceWords C n r).toFinset,
    (if xs ∈ (traceWords C n r).toFinset then traceMass sys σ t h y xs else 0)*
      (M.reward (run M t y s xs).1 (run M t y s xs).2 : ℝ)) = _
  calc
    _ = ∑ xs ∈ (traceWords C n r).toFinset,
        traceMass sys σ t h y xs*(M.reward (run M t y s xs).1 (run M t y s xs).2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro xs hx
      simp only [if_pos hx]
    _ = _ := List.sum_toFinset _ (traceWords_nodup r)

theorem chronologicalLaw_monitor_optimal_and_attained (sys : FiniteControlSystem C n)
    (M : Monitor C n S) (N : ℕ) (y : Fin n) :
    (∀ σ : BehavioralPolicy sys,
      (chronologicalLaw sys σ N 0 (y,[]) y).expectation
        (fun xs => (M.reward (run M 0 y (M.initial y) xs).1
          (run M 0 y (M.initial y) xs).2 : ℝ)) ≤ (value sys M N 0 y (M.initial y) : ℝ)) ∧
    (∃ σ : BehavioralPolicy sys,
      (chronologicalLaw sys σ N 0 (y,[]) y).expectation
        (fun xs => (M.reward (run M 0 y (M.initial y) xs).1
          (run M 0 y (M.initial y) xs).2 : ℝ)) = (value sys M N 0 y (M.initial y) : ℝ)) := by
  simpa only [chronologicalLaw_monitor_expectation] using monitor_optimal_and_attained sys M N y

end PermanssonResearch.ReverseSolver.FiniteMonitor
