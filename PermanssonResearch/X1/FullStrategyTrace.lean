import PermanssonResearch.X1.FullStrategyCertificate
import PermanssonResearch.Games.DiscountedTraceExpectation

/-! X1's exact performance difference on the canonical action-retaining law. -/

namespace PermanssonResearch.X1

open ActionTrace DiscountedVerification MeasureTheory
set_option autoImplicit false

/-- Same physical process and information; reward records extraction in depletion. -/
noncomputable def depletionGame (m : Mode) (i : Player) : Game Y Bool :=
  { strategyGame m i with reward := fun y a _ => if y.2 = false ∧ a = true then 1 else 0 }

theorem depletionGame_law (m : Mode) (i : Player) (σ : BehavioralPolicy Y Bool)
    (μ : Row Y) (n : ℕ) : law (depletionGame m i) σ μ n = law (strategyGame m i) σ μ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [law, law, ih]
      rfl

theorem depletionGame_canonical (m : Mode) (i : Player) (σ : BehavioralPolicy Y Bool)
    (μ : Row Y) : canonicalLaw (depletionGame m i) σ μ = canonicalLaw (strategyGame m i) σ μ := rfl

theorem depletionGame_reward_bound (m : Mode) (i : Player) (y : Y) (a b : Bool) :
    |(depletionGame m i).reward y a b| ≤ 1 := by
  change |if y.2 = false ∧ a = true then (1 : ℝ) else 0| ≤ 1
  split_ifs <;> norm_num

theorem depletionGame_stageReward (m : Mode) (i : Player) (σ : BehavioralPolicy Y Bool)
    (μ : Row Y) (n : ℕ) : stageReward (depletionGame m i) σ μ n =
      depletionExtractionProbability m i σ μ n := by
  unfold stageReward
  rw [depletionGame_law, law_step_expect]
  simp only [depletionGame, Row.expect_const]
  rfl

theorem depletionGame_payoff (m : Mode) (i : Player) (σ : BehavioralPolicy Y Bool)
    (μ : Row Y) : payoff (depletionGame m i) σ μ = discountedDepletionExtraction m i σ μ := by
  unfold payoff discountedDepletionExtraction
  simp_rw [depletionGame_stageReward]
  have hd : (depletionGame m i).discount = (9/10 : ℝ) := by
    norm_num [depletionGame, strategyGame, discount]
  rw [hd]

/-- Both indexed players and every initial law: the expected infinite discounted
reward differs from candidate value by exactly 9/211 times expected discounted
extraction in depletion. Both expectations use the actual retained actions. -/
theorem expected_exact_behavioral_performance_difference (m : Mode) (i : Player)
    (σ : BehavioralPolicy Y Bool) (μ : Row Y) :
    (∫ w, (∑' n, (9/10 : ℝ)^n * pathReward (strategyGame m i) n w)
      ∂canonicalLaw (strategyGame m i) σ μ) = μ.expect (strategyValue i) -
      (9/211 : ℝ) * (∫ w, (∑' n, (9/10 : ℝ)^n * pathReward (depletionGame m i) n w)
        ∂canonicalLaw (strategyGame m i) σ μ) := by
  have hmain := payoff_eq_expected_path_sum (strategyGame m i) σ μ (strategy_reward_bound m i)
  have hbad := payoff_eq_expected_path_sum (depletionGame m i) σ μ (depletionGame_reward_bound m i)
  have hd : (strategyGame m i).discount = (9/10 : ℝ) := by norm_num [strategyGame, discount]
  have hbd : (depletionGame m i).discount = (9/10 : ℝ) := by
    norm_num [depletionGame, strategyGame, discount]
  rw [hd] at hmain
  rw [hbd, depletionGame_canonical] at hbad
  rw [← hmain, ← hbad, depletionGame_payoff]
  exact exact_behavioral_performance_difference m i σ μ

end PermanssonResearch.X1
