import PermanssonResearch.ReverseSolver.BellmanPolicyValue
import Mathlib.Tactic

/-!
# D1-B: optimal recursive finite-horizon deterministic Markov control

Every admissible remaining-horizon Markov schedule is bounded by the
exact rational Bellman value. A statewise best control at each remaining
horizon constructs ONE schedule attaining that value simultaneously for
all finite horizons and all initial states. This theorem is about the
explicit policy recursion, not yet a nonstationary path measure.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace Bellman

open ControlledKernel

universe uC

/-- Pointwise monotonicity of the rational one-step continuation score. -/
theorem actionScore_mono {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (v w : Fin n → ℚ)
    (hvw : ∀ z, v z ≤ w z) (y : Fin n) (c : C) :
    actionScore sys v y c ≤ actionScore sys w y c := by
  unfold actionScore
  apply Finset.sum_le_sum
  intro z _
  exact mul_le_mul_of_nonneg_left (hvw z)
    ((sys.matrix c).entry_nonneg y z)

/-- Bellman value is an upper bound on EVERY admissible deterministic
time-dependent Markov schedule, for every horizon and initial state. -/
theorem policyValue_le_bellman {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) (π : MarkovSchedule sys) :
    ∀ (t : ℕ) (y : Fin n),
      policyValue sys target π t y ≤ bellmanValue sys target t y := by
  intro t
  induction t with
  | zero =>
      intro y
      rfl
  | succ t ih =>
      intro y
      rw [policyValue_succ, bellmanValue_succ]
      by_cases hg : y ∈ target.goal
      · simp [hg]
      · simp only [if_neg hg]
        by_cases hd : y ∈ target.forbidden
        · simp [hd]
        · simp only [if_neg hd]
          calc
            actionScore sys (policyValue sys target π t) y
                ((π (t+1)).choose y) ≤
              actionScore sys (bellmanValue sys target t) y
                ((π (t+1)).choose y) :=
                  actionScore_mono sys _ _ ih y _
            _ ≤ actionScore sys (bellmanValue sys target t) y
                (bestControl sys (bellmanValue sys target t) y) :=
                  bestControl_dominates sys (bellmanValue sys target t) y
                    ((π (t+1)).choose y) ((π (t+1)).permitted y)

/-- One time-dependent Markov policy: at t remaining transitions choose
a maximizer against Bellman value with t-1 transitions remaining.
The zero-horizon policy entry is irrelevant to terminal value. -/
noncomputable def maximizingSchedule {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) : MarkovSchedule sys :=
  fun remaining => bestFeedback sys
    (bellmanValue sys target (remaining - 1))

@[simp] theorem maximizingSchedule_succ_choose
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) (t : ℕ) (y : Fin n) :
    ((maximizingSchedule sys target (t+1)).choose y) =
      bestControl sys (bellmanValue sys target t) y := by
  simp [maximizingSchedule, bestFeedback]

/-- The maximizing schedule attains the Bellman value for EVERY finite
horizon and starting state, simultaneously. -/
theorem maximizingSchedule_attains {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) :
    ∀ (t : ℕ) (y : Fin n),
      policyValue sys target (maximizingSchedule sys target) t y =
        bellmanValue sys target t y := by
  intro t
  induction t with
  | zero =>
      intro y
      rfl
  | succ t ih =>
      intro y
      rw [policyValue_succ, bellmanValue_succ]
      by_cases hg : y ∈ target.goal
      · simp [hg]
      · simp only [if_neg hg]
        by_cases hd : y ∈ target.forbidden
        · simp [hd]
        · simp only [if_neg hd]
          rw [maximizingSchedule_succ_choose]
          unfold actionScore
          apply Finset.sum_congr rfl
          intro z _
          rw [ih z]

/-- The complete optimization claim: Bellman is an upper bound for ALL
declared policies and is attained by at least one admissible schedule. -/
theorem bellman_optimal_and_attained {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n) :
    (∀ (π : MarkovSchedule sys) (t : ℕ) (y : Fin n),
        policyValue sys target π t y ≤ bellmanValue sys target t y) ∧
    (∃ π : MarkovSchedule sys, ∀ (t : ℕ) (y : Fin n),
        policyValue sys target π t y = bellmanValue sys target t y) := by
  refine ⟨?_, ?_⟩
  · intro π t y
    exact policyValue_le_bellman sys target π t y
  · exact ⟨maximizingSchedule sys target, maximizingSchedule_attains sys target⟩

/-- If no goal exists, no admissible Markov policy succeeds at any horizon. -/
theorem bellmanValue_empty_goal {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n)
    (hg : target.goal = ∅) :
    ∀ (t : ℕ) (y : Fin n), bellmanValue sys target t y = 0 := by
  intro t
  induction t with
  | zero =>
      intro y
      simp [bellmanValue_zero, hg]
  | succ t ih =>
      intro y
      rw [bellmanValue_succ]
      have hnot : y ∉ target.goal := by simp [hg]
      simp only [if_neg hnot]
      by_cases hd : y ∈ target.forbidden
      · simp [hd]
      · simp only [if_neg hd]
        unfold actionScore
        simp [ih]

/-- With no forbidden states, Bellman is ordinary reachability recursion;
it need not equal one. -/
theorem bellmanValue_no_forbidden_succ
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n)
    (target : RationalHittingTarget n)
    (hd : target.forbidden = ∅)
    (t : ℕ) (y : Fin n) :
    bellmanValue sys target (t+1) y =
      if y ∈ target.goal then 1
      else actionScore sys (bellmanValue sys target t) y
        (bestControl sys (bellmanValue sys target t) y) := by
  rw [bellmanValue_succ]
  simp [hd]

end Bellman
end ReverseSolver
end PermanssonResearch
