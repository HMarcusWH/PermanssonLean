import PermanssonResearch.StrategicWorld.ActionTrace
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Discounted verification for every nonanticipating behavioral action rule

Finite expectations are taken under the explicit alternating-history laws.
The infinite scalar payoff is the absolutely convergent sum of those stage
expectations. No Markov or stationarity restriction is imposed on deviations.
-/

open scoped BigOperators
open Filter

namespace PermanssonResearch.DiscountedVerification

open ActionTrace

set_option autoImplicit false

universe u
variable {Y : Type u} {A : Type u} [Fintype Y] [Fintype A]

noncomputable def Q (G : Game Y A) (V : Y → ℝ) (y : Y) (a : A) : ℝ :=
  (G.opponent y).expect (fun b => G.reward y a b +
    G.discount * (G.physical y a b).expect V)

noncomputable def stageReward (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (n : ℕ) : ℝ :=
  (law G σ μ (n+1)).expect (fun h =>
    G.reward (last n h.1) h.2.1.1 h.2.1.2)

noncomputable def stateValue (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (V : Y → ℝ) (n : ℕ) : ℝ :=
  (law G σ μ n).expect (fun h => V (last n h))

noncomputable def stageLoss (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (V : Y → ℝ) (n : ℕ) : ℝ :=
  (law G σ μ n).expect (fun h =>
    (σ n h).expect (fun a => V (last n h) - Q G V (last n h) a))

/-- The actual finite trace law supplies the conditional Bellman identity. -/
theorem stage_balance (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (V : Y → ℝ) (n : ℕ) :
    stageReward G σ μ n + G.discount * stateValue G σ μ V (n+1) +
      stageLoss G σ μ V n = stateValue G σ μ V n := by
  classical
  have hnext : stageReward G σ μ n + G.discount * stateValue G σ μ V (n+1) =
      (law G σ μ n).expect (fun h => (σ n h).expect (fun a => Q G V (last n h) a)) := by
    unfold stageReward stateValue
    rw [← Row.expect_mul, ← Row.expect_add, law_step_expect]
    congr 1
    funext h
    congr 1
    funext a
    unfold Q
    congr 1
    funext b
    simp only [last, Row.expect_add, Row.expect_const, Row.expect_mul]
  rw [hnext]
  unfold stageLoss stateValue
  rw [← Row.expect_add]
  simp [Row.expect_sub]

noncomputable def finitePayoff (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (n : ℕ) : ℝ := ∑ t ∈ Finset.range n, G.discount^t * stageReward G σ μ t

noncomputable def finiteLoss (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (V : Y → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, G.discount^t * stageLoss G σ μ V t

/-- Exact telescoping retains the terminal value; this is valid for every
history-dependent behavioral policy, including time-dependent ones. -/
theorem finite_performance_difference (G : Game Y A) (σ : BehavioralPolicy Y A)
    (μ : Row Y) (V : Y → ℝ) (n : ℕ) :
    finitePayoff G σ μ n + finiteLoss G σ μ V n +
      G.discount^n * stateValue G σ μ V n = μ.expect V := by
  induction n with
  | zero => simp [finitePayoff, finiteLoss, stateValue, law, last]
  | succ n ih =>
      simp only [finitePayoff, finiteLoss, Finset.sum_range_succ] at *
      have h := stage_balance G σ μ V n
      have hm := congrArg (fun x : ℝ => G.discount^n * x) h
      rw [pow_succ]
      nlinarith [hm]

/-- Convex combinations preserve every pure-action Bellman inequality. -/
theorem stageLoss_nonneg (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (V : Y → ℝ) (hV : ∀ y a, Q G V y a ≤ V y) (n : ℕ) :
    0 ≤ stageLoss G σ μ V n := by
  unfold stageLoss
  unfold Row.expect
  apply Finset.sum_nonneg
  intro h _
  apply mul_nonneg ((law G σ μ n).nonneg h)
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg ((σ n h).nonneg a) (sub_nonneg.mpr (hV (last n h) a))

theorem finite_verification (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (V : Y → ℝ) (hV : ∀ y a, Q G V y a ≤ V y) (n : ℕ) :
    finitePayoff G σ μ n + G.discount^n * stateValue G σ μ V n ≤ μ.expect V := by
  have h := finite_performance_difference G σ μ V n
  have hl : 0 ≤ finiteLoss G σ μ V n :=
    Finset.sum_nonneg (fun t _ => mul_nonneg (pow_nonneg G.discount_nonneg _)
      (stageLoss_nonneg G σ μ V hV t))
  linarith

theorem stageReward_abs_le (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    {R : ℝ} (hR : ∀ y a b, |G.reward y a b| ≤ R) (n : ℕ) :
    |stageReward G σ μ n| ≤ R :=
  (law G σ μ (n+1)).abs_expect_le (fun h => hR _ _ _)

theorem stateValue_abs_le (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (V : Y → ℝ) {C : ℝ} (hC : ∀ y, |V y| ≤ C) (n : ℕ) :
    |stateValue G σ μ V n| ≤ C :=
  (law G σ μ n).abs_expect_le (fun h => hC _)

/-- Explicit terminal correction bound, including nonstationary policies. -/
theorem terminal_bound (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (V : Y → ℝ) {C : ℝ} (hC : ∀ y, |V y| ≤ C) (n : ℕ) :
    |G.discount^n * stateValue G σ μ V n| ≤ C * G.discount^n := by
  rw [abs_mul, abs_of_nonneg (pow_nonneg G.discount_nonneg _), mul_comm C]
  exact mul_le_mul_of_nonneg_left (stateValue_abs_le G σ μ V hC n)
    (pow_nonneg G.discount_nonneg _)

theorem summable_rewards (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    {R : ℝ} (hR : ∀ y a b, |G.reward y a b| ≤ R) :
    Summable (fun t => G.discount^t * stageReward G σ μ t) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one G.discount_nonneg G.discount_lt_one).mul_right R)
  intro t
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg G.discount_nonneg _)]
  exact mul_le_mul_of_nonneg_left (stageReward_abs_le G σ μ hR t)
    (pow_nonneg G.discount_nonneg _)

/-- Discounted scalar payoff under the projectively consistent action-trace
laws. The summability theorem justifies this series without a supremum swap. -/
noncomputable def payoff (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y) : ℝ :=
  ∑' t, G.discount^t * stageReward G σ μ t

theorem finitePayoff_tendsto (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    {R : ℝ} (hR : ∀ y a b, |G.reward y a b| ≤ R) :
    Tendsto (finitePayoff G σ μ) atTop (nhds (payoff G σ μ)) := by
  exact (summable_rewards G σ μ hR).hasSum.tendsto_sum_nat

theorem terminal_tendsto_zero (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (V : Y → ℝ) {C : ℝ} (hC : ∀ y, |V y| ≤ C) :
    Tendsto (fun n => G.discount^n * stateValue G σ μ V n) atTop (nhds 0) := by
  apply squeeze_zero_norm' (Filter.Eventually.of_forall (fun n =>
    (show ‖G.discount^n * stateValue G σ μ V n‖ ≤ C * G.discount^n by
      simpa only [Real.norm_eq_abs] using terminal_bound G σ μ V hC n)))
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
    G.discount_nonneg G.discount_lt_one).const_mul C

/-- Infinite-horizon verification, quantified over ALL behavioral rules on
complete histories and all real-probability initial laws. -/
theorem discounted_verification (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (V : Y → ℝ) {R C : ℝ} (hR : ∀ y a b, |G.reward y a b| ≤ R)
    (hC : ∀ y, |V y| ≤ C) (hV : ∀ y a, Q G V y a ≤ V y) :
    payoff G σ μ ≤ μ.expect V := by
  have hp := (finitePayoff_tendsto G σ μ hR).add
    (terminal_tendsto_zero G σ μ V hC)
  have hh := le_of_tendsto hp
    (Filter.Eventually.of_forall (finite_verification G σ μ V hV))
  simpa using hh

/-- Bellman equality at every observed history implies exact attainment. -/
theorem discounted_attainment (G : Game Y A) (π : BehavioralPolicy Y A) (μ : Row Y)
    (V : Y → ℝ) {R C : ℝ} (hR : ∀ y a b, |G.reward y a b| ≤ R)
    (hC : ∀ y, |V y| ≤ C)
    (hπ : ∀ n h, (π n h).expect (fun a => Q G V (last n h) a) = V (last n h)) :
    payoff G π μ = μ.expect V := by
  have hzero (n : ℕ) : stageLoss G π μ V n = 0 := by
    unfold stageLoss
    simp only [Row.expect_sub, Row.expect_const, hπ, sub_self]
  have heq (n : ℕ) : finitePayoff G π μ n +
      G.discount^n * stateValue G π μ V n = μ.expect V := by
    simpa [finiteLoss, hzero] using finite_performance_difference G π μ V n
  have hp := (finitePayoff_tendsto G π μ hR).add
    (terminal_tendsto_zero G π μ V hC)
  have hc : Tendsto (fun _ : ℕ => μ.expect V) atTop (nhds (μ.expect V)) := tendsto_const_nhds
  have hh := tendsto_nhds_unique hp (by simpa only [heq] using hc)
  simpa using hh

/-- Every individual pure continuation expectation is bounded using the
declared reward and candidate-value bounds. -/
theorem Q_abs_le (G : Game Y A) (V : Y → ℝ) {R C : ℝ}
    (hR : ∀ y a b, |G.reward y a b| ≤ R) (hC : ∀ y, |V y| ≤ C)
    (y : Y) (a : A) : |Q G V y a| ≤ R + G.discount * C := by
  apply (G.opponent y).abs_expect_le
  intro b
  calc
    |G.reward y a b + G.discount * (G.physical y a b).expect V| ≤
        |G.reward y a b| + |G.discount * (G.physical y a b).expect V| := abs_add_le _ _
    _ ≤ R + G.discount * C := by
      rw [abs_mul, abs_of_nonneg G.discount_nonneg]
      exact add_le_add (hR y a b) (mul_le_mul_of_nonneg_left
        ((G.physical y a b).abs_expect_le hC) G.discount_nonneg)

theorem stageLoss_abs_le (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (V : Y → ℝ) {R C : ℝ} (hR : ∀ y a b, |G.reward y a b| ≤ R)
    (hC : ∀ y, |V y| ≤ C) (n : ℕ) :
    |stageLoss G σ μ V n| ≤ C + (R + G.discount * C) := by
  apply (law G σ μ n).abs_expect_le
  intro h
  apply (σ n h).abs_expect_le
  intro a
  exact (abs_sub _ _).trans (add_le_add (hC _) (Q_abs_le G V hR hC _ a))

theorem summable_losses (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    (V : Y → ℝ) {R C : ℝ} (hR : ∀ y a b, |G.reward y a b| ≤ R)
    (hC : ∀ y, |V y| ≤ C) :
    Summable (fun n => G.discount^n * stageLoss G σ μ V n) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one G.discount_nonneg G.discount_lt_one).mul_right
      (C + (R + G.discount * C)))
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg G.discount_nonneg _)]
  exact mul_le_mul_of_nonneg_left (stageLoss_abs_le G σ μ V hR hC n)
    (pow_nonneg G.discount_nonneg _)

/-- Exact infinite performance difference; the loss is not replaced by a
nonnegative upper bound. -/
theorem infinite_performance_difference (G : Game Y A) (σ : BehavioralPolicy Y A)
    (μ : Row Y) (V : Y → ℝ) {R C : ℝ} (hR : ∀ y a b, |G.reward y a b| ≤ R)
    (hC : ∀ y, |V y| ≤ C) :
    payoff G σ μ + (∑' n, G.discount^n * stageLoss G σ μ V n) = μ.expect V := by
  have hl : Tendsto (finiteLoss G σ μ V) atTop
      (nhds (∑' n, G.discount^n * stageLoss G σ μ V n)) :=
    (summable_losses G σ μ V hR hC).hasSum.tendsto_sum_nat
  have ht := ((finitePayoff_tendsto G σ μ hR).add hl).add
    (terminal_tendsto_zero G σ μ V hC)
  have hc : Tendsto (fun _ : ℕ => μ.expect V) atTop (nhds (μ.expect V)) :=
    tendsto_const_nhds
  have heq := tendsto_nhds_unique ht
    (by simpa only [finite_performance_difference] using hc)
  simpa using heq

/-- Uniform geometric payoff tail; the terminal correction has its separate
bound above and is never silently discarded at finite horizon. -/
theorem payoff_tail_bound (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    {R : ℝ} (hR : ∀ y a b, |G.reward y a b| ≤ R) (n : ℕ) :
    |payoff G σ μ - finitePayoff G σ μ n| ≤
      R * G.discount^n / (1-G.discount) := by
  have hsum := (summable_rewards G σ μ hR).sum_add_tsum_nat_add n
  have heq : payoff G σ μ - finitePayoff G σ μ n =
      ∑' t, G.discount^(t+n) * stageReward G σ μ (t+n) := by
    dsimp [payoff, finitePayoff] at *
    linarith
  rw [heq]
  have hgeo := (hasSum_geometric_of_lt_one G.discount_nonneg G.discount_lt_one).mul_left
    (R * G.discount^n)
  have hbound : ∀ t, ‖G.discount^(t+n) * stageReward G σ μ (t+n)‖ ≤
      (R * G.discount^n) * G.discount^t := by
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg G.discount_nonneg _)]
    calc
      _ ≤ G.discount^(t+n) * R := mul_le_mul_of_nonneg_left
        (stageReward_abs_le G σ μ hR _) (pow_nonneg G.discount_nonneg _)
      _ = _ := by rw [pow_add]; ring
  have hh := tsum_of_norm_bounded hgeo hbound
  simpa only [Real.norm_eq_abs, one_div, div_eq_mul_inv] using hh

end PermanssonResearch.DiscountedVerification
