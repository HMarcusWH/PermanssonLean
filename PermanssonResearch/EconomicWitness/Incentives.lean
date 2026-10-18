import PermanssonResearch.EconomicWitness.Model

/-! Both-player economic incentives against every behavioral history deviation. -/

namespace PermanssonResearch.EconomicWitness
open ActionTrace DiscountedVerification MeasureTheory
set_option autoImplicit false

theorem exact_advantage (i : Player) (y : Y) (a : Bool) :
    value i y - Q (strategyGame i) (value i) y a =
      if y.2 ≠ 2 ∧ a = true then (2 : ℝ) else 0 := by
  rcases y with ⟨u,x⟩
  cases u
  fin_cases i <;> fin_cases x <;> cases a <;>
    norm_num [Q, strategyGame, worldRow, Row.expect, Row.map, Row.pure,
      fairRow, value, reward, assemble, ownAction, Fin.sum_univ_three,
      Fintype.sum_prod_type]

theorem pure_bellman (i : Player) (y : Y) (a : Bool) :
    Q (strategyGame i) (value i) y a ≤ value i y := by
  have h := exact_advantage i y a
  split_ifs at h <;> linarith

theorem reward_bound (i : Player) (y : Y) (a b : Bool) :
    |(strategyGame i).reward y a b| ≤ 2 := by
  rcases y with ⟨u,x⟩
  fin_cases i <;> fin_cases x <;> cases a <;> cases b <;>
    norm_num [strategyGame, reward, ownAction, assemble]

theorem value_bound (i : Player) (y : Y) : |value i y| ≤ 4 := by
  unfold value
  split_ifs <;> norm_num

theorem baseline_bellman (i : Player) (n : ℕ) (h : History Y (Bool × Bool) n) :
    (baselineBehavior n h).expect (fun a => Q (strategyGame i) (value i) (last n h) a) =
      value i (last n h) := by
  simp only [baselineBehavior, Row.expect_pure]
  have hh := exact_advantage i (last n h) false
  simp only [Bool.false_eq_true, and_false, if_false] at hh
  linarith

/-- Global optimality for both players, all starts and every nonanticipating
real behavioral rule. Current opponent/future noise are absent from its domain. -/
theorem full_behavioral_optimality (i : Player) (σ : BehavioralPolicy Y Bool) (μ : Row Y) :
    payoff (strategyGame i) σ μ ≤ μ.expect (value i) :=
  discounted_verification _ _ _ _ (reward_bound i) (value_bound i) (pure_bellman i)

theorem baseline_attainment (i : Player) (μ : Row Y) :
    payoff (strategyGame i) baselineBehavior μ = μ.expect (value i) :=
  discounted_attainment _ _ _ _ (reward_bound i) (value_bound i) (baseline_bellman i)

theorem expected_behavioral_optimality (i : Player) (σ : BehavioralPolicy Y Bool) (μ : Row Y) :
    (∫ w, (∑' n, (3/4 : ℝ)^n * pathReward (strategyGame i) n w)
      ∂canonicalLaw (strategyGame i) σ μ) ≤ μ.expect (value i) := by
  exact expected_discounted_verification _ _ _ _
    (reward_bound i) (value_bound i) (pure_bellman i)

/-- Changing the functioning extraction reward to five destroys the intended
Bellman inequality at value four. -/
theorem altered_reward_rejected : ¬ ((5 : ℝ) + (3/4 : ℝ) * 0 ≤ 4) := by norm_num

end PermanssonResearch.EconomicWitness
