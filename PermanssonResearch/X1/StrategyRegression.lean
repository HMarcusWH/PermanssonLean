import PermanssonResearch.X1.FullStrategyCertificate
import PermanssonResearch.StrategicWorld.ActionTraceStatePrefix

/-! Theorem-level positive and adversarial strategy regressions. -/

namespace PermanssonResearch.X1.StrategyRegression

open ActionTrace DiscountedVerification

/-- Exhausts every Boolean state-dependent pure deviation (four maps), both
players, both declared updates and every one of the eighteen initial states. -/
noncomputable def pureStateDeviation (f : Bool → Bool) : BehavioralPolicy Y Bool :=
  fun n h => Row.pure (f (last n h).2)

theorem all_pure_state_deviations (m : Mode) (i : Player) (f : Bool → Bool) (y : Y) :
    payoff (strategyGame m i) (pureStateDeviation f) (Row.pure y) ≤ (value i y.2 : ℝ) := by
  simpa only [Row.expect_pure, strategyValue]
    using full_behavioral_verification m i (pureStateDeviation f) (Row.pure y)

/-- A time-dependent deviation is covered, including the terminal correction. -/
theorem nonstationary_terminal_identity (m : Mode) (i : Player) (y : Y) (n : ℕ) :
    finitePayoff (strategyGame m i) alternatingDeviation (Row.pure y) n +
      finiteLoss (strategyGame m i) alternatingDeviation (Row.pure y) (strategyValue i) n +
      (9/10 : ℝ)^n * stateValue (strategyGame m i) alternatingDeviation
        (Row.pure y) (strategyValue i) n = (value i y.2 : ℝ) :=
  alternatingDeviation_finite_identity m i y n

/-- The wrong discount fails the intended pure-action Bellman requirement;
it is not rejected merely by a parser or artifact checksum. -/
theorem wrong_discount_rejected : value 0 false < reward 0 false (false,false) +
    (8/10 : ℚ) * continuation 0 false (false,false) := by
  norm_num [value, reward, ownAction, otherAction, indicator, congestion,
    depletionCost, continuation, pRep]

/-- Altering the depleted physical world row to one-half likewise fails the
candidate-value Bellman inequality at restraint. -/
theorem altered_world_row_rejected : value 0 false < reward 0 false (false,false) +
    discount * ((1/2 : ℚ) * value 0 true + (1/2 : ℚ) * value 0 false) := by
  norm_num [value, reward, ownAction, otherAction, indicator, congestion,
    depletionCost, discount]

theorem altered_reward_rejected : value 0 false < 1 + reward 0 false (false,false) +
    discount * continuation 0 false (false,false) := by
  norm_num [value,reward,ownAction,otherAction,indicator,congestion,
    depletionCost,continuation,pRep,discount]

/-- Two action histories can have the same entire observed state prefix while
carrying different actual rewards. Erasure cannot define this reward. -/
theorem reward_cannot_factor_through_state_prefix :
    ¬ ∃ f : StatePrefix Y 1 → ℝ,
      ∀ h : History Y (Bool × Bool) 1,
        (strategyGame .equilibrium 0).reward (last 0 h.1) h.2.1.1 h.2.1.2 =
          f (states 1 h) := by
  rintro ⟨f,hf⟩
  let h0 : History Y (Bool × Bool) 1 := (y0,((false,false),y0))
  let h1 : History Y (Bool × Bool) 1 := (y0,((true,false),y0))
  have hzero := hf h0
  have hone := hf h1
  have heq : states 1 h0 = states 1 h1 := rfl
  rw [heq] at hzero
  have hh := hzero.trans hone.symm
  norm_num [h0,h1,last,strategyGame,y0,reward,deviationAction,
    ownAction,otherAction,indicator,congestion,depletionCost] at hh

/-- The realized current opponent draw is not in the strategy's domain. A
would-be function of that draw has a different type and requires a separate
information structure. -/
def history_restriction (n : ℕ) :
    BehavioralPolicy Y Bool → (History Y (Bool × Bool) n → Row Bool) :=
  fun σ => σ n

theorem discounted_depletion_nonnegative (m : Mode) (i : Player)
    (σ : BehavioralPolicy Y Bool) (μ : Row Y) :
    0 ≤ discountedDepletionExtraction m i σ μ := by
  have hi := exact_behavioral_performance_difference m i σ μ
  have hv := full_behavioral_verification m i σ μ
  nlinarith

/-- The exact equality condition does not assert uniqueness: actions in the
replete world remain free whenever the discounted depletion-extraction cost
has expectation zero. -/
theorem performance_equality_iff (m : Mode) (i : Player)
    (σ : BehavioralPolicy Y Bool) (μ : Row Y) :
    payoff (strategyGame m i) σ μ = μ.expect (strategyValue i) ↔
      discountedDepletionExtraction m i σ μ = 0 := by
  rw [exact_behavioral_performance_difference]
  constructor
  · intro hh
    nlinarith
  · intro hh
    rw [hh]
    ring

end PermanssonResearch.X1.StrategyRegression
