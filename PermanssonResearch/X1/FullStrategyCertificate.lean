import PermanssonResearch.Games.DiscountedVerification
import PermanssonResearch.X1.MPECertificate
import PermanssonResearch.X1.TypedModels

/-!
# X1 full-history performance-difference ingredients

Both indexed players, all memory/world states, and arbitrary real behavioral
rows use the actual fixed P and the declared update for either mode.
-/

namespace PermanssonResearch.X1

open ActionTrace DiscountedVerification

set_option autoImplicit false

/-- The exact eight-case advantage table; no symmetry argument substitutes for
either player's certificate. -/
theorem exact_advantage_table (i : Player) (x a : Bool) :
    value i x - deviationValue i x a =
      if x = false ∧ a = true then (9 / 211 : ℚ) else 0 := by
  fin_cases i <;> cases x <;> cases a <;>
    norm_num [deviationValue, deviationAction, piAction, piExtract, boolMass,
      value, reward, ownAction, otherAction, indicator, continuation, pRep,
      discount, congestion, depletionCost]

/-- All actual stage rewards obey the deliberately simple paper bound. -/
theorem reward_abs_le_two (i : Player) (x : Bool) (a : Action) :
    |reward i x a| ≤ 2 := by
  rcases a with ⟨a,b⟩
  fin_cases i <;> cases x <;> cases a <;> cases b <;>
    norm_num [reward, ownAction, otherAction, indicator, congestion, depletionCost]

theorem value_abs_le_one (i : Player) (x : Bool) : |value i x| ≤ 1 := by
  cases x <;> norm_num [value]

/-- A real-probability Boolean row, reused for actual P and fixed π. -/
noncomputable def booleanRow (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) : Row Bool where
  mass b := (boolMass p b : ℝ)
  nonneg b := by
    cases b
    · exact_mod_cast sub_nonneg.mpr hp.2
    · exact_mod_cast hp.1
  total := by
    rw [sum_bool]
    simp only [boolMass, Bool.false_eq_true, ↓reduceIte]
    push_cast
    ring

@[simp] theorem booleanRow_expect (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (f : Bool → ℝ) :
    (booleanRow p hp).expect f = (1-(p:ℝ)) * f false + (p:ℝ) * f true := by
  simp only [Row.expect, sum_bool, booleanRow, boolMass]
  push_cast
  ring

/-- Literal equality with the Boolean probability law used by TypedModels. -/
theorem booleanRow_measure_eq_coin (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (booleanRow p hp).measure = coin p := by
  apply MeasureTheory.Measure.ext_of_singleton
  intro b
  rw [Row.measure_singleton]
  cases b
  · simpa [booleanRow, boolMass] using (coin_false p).symm
  · simpa [booleanRow, boolMass] using (coin_true p).symm

/-- The actual X1 physical step after sampled own/opponent actions. Its
memory update has the same old-world/action timing as `TypedModels`. -/
noncomputable def strategyGame (m : Mode) (i : Player) : Game Y Bool where
  player := i
  physical y a b := (booleanRow (pRep y.2 (deviationAction i a b))
    (pRep_bounds _ _)).map (fun x => (nextMemory m y (deviationAction i a b),x))
  opponent y := booleanRow (piExtract y.2) (piExtract_bounds _)
  reward y a b := (reward i y.2 (deviationAction i a b) : ℝ)
  discount := (discount : ℝ)
  discount_nonneg := by norm_num [discount]
  discount_lt_one := by norm_num [discount]

noncomputable def strategyValue (i : Player) (y : Y) : ℝ := (value i y.2 : ℝ)

/-- Exact all-observable adapter to the actual physical P→U law. The action
draw is already recorded, and the actual update reads the old world/action.
This is not a separately postulated transition matrix. -/
theorem strategy_physical_expect_actual (m : Mode) (i : Player) (y : Y)
    (a b : Bool) (f : Y → ℝ) :
    ((strategyGame m i).physical y a b).expect f =
      ∫ x, ∫ q, f (q,x) ∂update m ((y,deviationAction i a b),x)
        ∂world (y,deviationAction i a b) := by
  simp only [strategyGame, Row.expect_map]
  rw [Row.expect_eq_integral, booleanRow_measure_eq_coin]
  change (∫ x, f (nextMemory m y (deviationAction i a b),x)
    ∂coin (pRep y.2 (deviationAction i a b))) = _
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro x
  simp [update, ProbabilityTheory.Kernel.deterministic_apply]

/-- The generic one-shot expectation is exactly the existing rational X1
Bellman quantity, for all memory coordinates and both declared updates. -/
theorem strategy_Q_eq (m : Mode) (i : Player) (y : Y) (a : Bool) :
    Q (strategyGame m i) (strategyValue i) y a = (deviationValue i y.2 a : ℝ) := by
  simp only [Q, strategyGame, Row.expect_map, strategyValue, booleanRow_expect]
  unfold deviationValue continuation piAction boolMass
  simp only [Bool.false_eq_true, ↓reduceIte]
  push_cast
  ring

theorem strategy_exact_advantage (m : Mode) (i : Player) (y : Y) (a : Bool) :
    strategyValue i y - Q (strategyGame m i) (strategyValue i) y a =
      if y.2 = false ∧ a = true then (9 / 211 : ℝ) else 0 := by
  rw [strategy_Q_eq]
  rcases y with ⟨q,x⟩
  fin_cases i <;> cases x <;> cases a <;>
    norm_num [strategyValue, deviationValue, deviationAction, piAction, piExtract, boolMass,
      value, reward, ownAction, otherAction, indicator, continuation, pRep,
      discount, congestion, depletionCost]

/-- A time-dependent policy is accepted without changing the information
structure: odd dates extract and even dates restrain. -/
noncomputable def alternatingDeviation : BehavioralPolicy Y Bool :=
  fun n _ => Row.pure (n % 2 == 1)

/-- The X1 baseline independent own policy, embedded in the full history class. -/
noncomputable def baselineBehavior : BehavioralPolicy Y Bool :=
  fun n h => booleanRow (piExtract (last n h).2) (piExtract_bounds _)

theorem strategy_reward_bound (m : Mode) (i : Player) (y : Y) (a b : Bool) :
    |(strategyGame m i).reward y a b| ≤ 2 := by
  change |(reward i y.2 (deviationAction i a b) : ℝ)| ≤ 2
  exact_mod_cast reward_abs_le_two i y.2 (deviationAction i a b)

theorem strategy_value_bound (i : Player) (y : Y) : |strategyValue i y| ≤ 1 := by
  change |(value i y.2 : ℝ)| ≤ 1
  exact_mod_cast value_abs_le_one i y.2

theorem strategy_bellman (m : Mode) (i : Player) (y : Y) (a : Bool) :
    Q (strategyGame m i) (strategyValue i) y a ≤ strategyValue i y := by
  rw [strategy_Q_eq]
  change (deviationValue i y.2 a : ℝ) ≤ (value i y.2 : ℝ)
  exact_mod_cast no_pure_deviation i y.2 a

theorem baseline_behavior_bellman (m : Mode) (i : Player) (n : ℕ)
    (h : History Y (Bool × Bool) n) :
    (baselineBehavior n h).expect (fun a =>
      Q (strategyGame m i) (strategyValue i) (last n h) a) =
        strategyValue i (last n h) := by
  simp only [baselineBehavior, booleanRow_expect, strategy_Q_eq, strategyValue]
  have heq (x : Bool) :
      (1-piExtract x) * deviationValue i x false +
        piExtract x * deviationValue i x true = value i x := by
    fin_cases i <;> cases x <;>
      norm_num [deviationValue, deviationAction, piAction, piExtract, boolMass,
        value, reward, ownAction, otherAction, indicator, continuation, pRep,
        discount, congestion, depletionCost]
  exact_mod_cast heq (last n h).2

/-- Both indexed X1 players: no arbitrary nonanticipating behavioral history
rule improves the scalar discounted finite-trace payoff from any initial law. -/
theorem full_behavioral_verification (m : Mode) (i : Player)
    (σ : BehavioralPolicy Y Bool) (μ : Row Y) :
    payoff (strategyGame m i) σ μ ≤ μ.expect (strategyValue i) :=
  discounted_verification _ _ _ _ (strategy_reward_bound m i) (strategy_value_bound i)
    (strategy_bellman m i)

/-- The candidate π baseline attains the same value for every initial law.
For `m = equilibrium` this is the original equilibrium model's action/update
choice; the learner update case still keeps π actions and is not a claim
about the original learner-action baseline's equilibrium incentives. -/
theorem baseline_behavior_attains (m : Mode) (i : Player) (μ : Row Y) :
    payoff (strategyGame m i) baselineBehavior μ = μ.expect (strategyValue i) :=
  discounted_attainment _ _ _ _ (strategy_reward_bound m i) (strategy_value_bound i)
    (baseline_behavior_bellman m i)

noncomputable def depletionExtractionProbability (m : Mode) (i : Player)
    (σ : BehavioralPolicy Y Bool) (μ : Row Y) (n : ℕ) : ℝ :=
  (law (strategyGame m i) σ μ n).expect (fun h =>
    (σ n h).expect (fun a => if (last n h).2 = false ∧ a = true then 1 else 0))

theorem stageLoss_eq_depletion_extraction (m : Mode) (i : Player)
    (σ : BehavioralPolicy Y Bool) (μ : Row Y) (n : ℕ) :
    stageLoss (strategyGame m i) σ μ (strategyValue i) n =
      (9/211 : ℝ) * depletionExtractionProbability m i σ μ n := by
  unfold stageLoss depletionExtractionProbability
  simp_rw [strategy_exact_advantage]
  have hh (x a : Bool) :
      (if x = false ∧ a = true then (9/211 : ℝ) else 0) =
        (9/211 : ℝ) * (if x = false ∧ a = true then 1 else 0) := by
    split_ifs <;> ring
  simp_rw [hh, Row.expect_mul]

/-- Expected discounted extraction in depletion under the complete finite
action-trace laws. It is nonnegative and can vanish for many distinct rules. -/
noncomputable def discountedDepletionExtraction (m : Mode) (i : Player)
    (σ : BehavioralPolicy Y Bool) (μ : Row Y) : ℝ :=
  ∑' n, (9/10 : ℝ)^n * depletionExtractionProbability m i σ μ n

/-- The stronger exact identity, for both indexed players and every full
history rule. It does not claim uniqueness of best responses. -/
theorem exact_behavioral_performance_difference (m : Mode) (i : Player)
    (σ : BehavioralPolicy Y Bool) (μ : Row Y) :
    payoff (strategyGame m i) σ μ = μ.expect (strategyValue i) -
      (9/211 : ℝ) * discountedDepletionExtraction m i σ μ := by
  have hh := infinite_performance_difference (strategyGame m i) σ μ (strategyValue i)
    (strategy_reward_bound m i) (strategy_value_bound i)
  have heq : (∑' n, (strategyGame m i).discount^n *
      stageLoss (strategyGame m i) σ μ (strategyValue i) n) =
        (9/211 : ℝ) * discountedDepletionExtraction m i σ μ := by
    simp_rw [stageLoss_eq_depletion_extraction]
    simp only [strategyGame, discount, Rat.cast_div, Rat.cast_ofNat,
      discountedDepletionExtraction]
    simp_rw [mul_left_comm _ (9/211 : ℝ)]
    rw [tsum_mul_left]
  rw [heq] at hh
  linarith

theorem exact_behavioral_performance_difference_start (m : Mode) (i : Player)
    (σ : BehavioralPolicy Y Bool) (y : Y) :
    payoff (strategyGame m i) σ (Row.pure y) = (value i y.2 : ℝ) -
      (9/211 : ℝ) * discountedDepletionExtraction m i σ (Row.pure y) := by
  simpa only [Row.expect_pure, strategyValue]
    using exact_behavioral_performance_difference m i σ (Row.pure y)

/-- A concrete time-varying admissible rule passes the same finite identity,
with its terminal correction present at every horizon. -/
theorem alternatingDeviation_finite_identity (m : Mode) (i : Player) (y : Y) (n : ℕ) :
    finitePayoff (strategyGame m i) alternatingDeviation (Row.pure y) n +
      finiteLoss (strategyGame m i) alternatingDeviation (Row.pure y) (strategyValue i) n +
      (9/10 : ℝ)^n * stateValue (strategyGame m i) alternatingDeviation
        (Row.pure y) (strategyValue i) n = (value i y.2 : ℝ) := by
  simpa only [Row.expect_pure, strategyValue, strategyGame, discount,
    Rat.cast_div, Rat.cast_ofNat] using finite_performance_difference
      (strategyGame m i) alternatingDeviation (Row.pure y) (strategyValue i) n

end PermanssonResearch.X1
