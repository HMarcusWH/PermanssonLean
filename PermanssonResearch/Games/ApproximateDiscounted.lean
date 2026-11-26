import PermanssonResearch.Games.DiscountedVerification
import PermanssonResearch.Games.DiscountedTraceExpectation

/-! Approximate verification on the existing complete alternating histories.
Candidate policy evaluation and unilateral continuation regret are separate
uniform residuals. No equilibrium search or private-information result. -/
namespace PermanssonResearch.ApproxEquilibrium

open ActionTrace DiscountedVerification
open scoped BigOperators
open Filter
set_option autoImplicit false

universe u
variable {Y A : Type u} [Fintype Y] [Fintype A]

/-- Every stage loss is bounded below by the one-step Bellman violation. -/
theorem stageLoss_lower (G : Game Y A) (σ : BehavioralPolicy Y A)
    (μ : Row Y) (V : Y → ℝ) (η : ℝ)
    (h : ∀ y a, Q G V y a - V y ≤ η) (n : ℕ) :
    -η ≤ stageLoss G σ μ V n := by
  unfold stageLoss
  have hinner : ∀ hist : History Y (A × A) n,
      -η ≤ (σ n hist).expect (fun a => V (last n hist) - Q G V (last n hist) a) := by
    intro hist
    have hb := (σ n hist).expect_mono
      (f := fun _ => -η) (g := fun a => V (last n hist) - Q G V (last n hist) a)
      (fun a => by linarith [h (last n hist) a])
    simpa using hb
  simpa using (law G σ μ n).expect_mono (f := fun _ => -η) hinner

theorem stageLoss_upper (G : Game Y A) (π : BehavioralPolicy Y A)
    (μ : Row Y) (V : Y → ℝ) (η : ℝ)
    (h : ∀ n hist, V (last n hist) -
      (π n hist).expect (fun a => Q G V (last n hist) a) ≤ η) (n : ℕ) :
    stageLoss G π μ V n ≤ η := by
  unfold stageLoss
  have hinner : ∀ hist : History Y (A × A) n,
      (π n hist).expect (fun a => V (last n hist) - Q G V (last n hist) a) ≤ η := by
    intro hist
    simpa only [Row.expect_sub, Row.expect_const] using h n hist
  simpa using (law G π μ n).expect_mono (g := fun _ => η) hinner

/-- One-sided residuals suffice; the same initial law and opponent are used. -/
theorem discounted_two_residual_bound (G : Game Y A) (σ π : BehavioralPolicy Y A)
    (μ : Row Y) (V : Y → ℝ) {R C : ℝ}
    (hR : ∀ y a b, |G.reward y a b| ≤ R) (hC : ∀ y, |V y| ≤ C)
    (ηplus ηminus : ℝ)
    (hplus : ∀ y a, Q G V y a - V y ≤ ηplus)
    (hminus : ∀ n hist, V (last n hist) -
      (π n hist).expect (fun a => Q G V (last n hist) a) ≤ ηminus) :
    payoff G σ μ - payoff G π μ ≤ (ηplus+ηminus)/(1-G.discount) := by
  have hs := summable_losses G σ μ V hR hC
  have hp := summable_losses G π μ V hR hC
  have hlow := (hasSum_geometric_of_lt_one G.discount_nonneg G.discount_lt_one).mul_right (-ηplus)
  have hhigh := (hasSum_geometric_of_lt_one G.discount_nonneg G.discount_lt_one).mul_right ηminus
  have hl := Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (stageLoss_lower G σ μ V ηplus hplus n)
      (pow_nonneg G.discount_nonneg n)) hlow.summable hs
  have hu := Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (stageLoss_upper G π μ V ηminus hminus n)
      (pow_nonneg G.discount_nonneg n)) hp hhigh.summable
  rw [hlow.tsum_eq] at hl
  rw [hhigh.tsum_eq] at hu
  have e1 := infinite_performance_difference G σ μ V hR hC
  have e2 := infinite_performance_difference G π μ V hR hC
  have hdiff :
      payoff G σ μ - payoff G π μ =
        (∑' n, G.discount^n * stageLoss G π μ V n) -
        (∑' n, G.discount^n * stageLoss G σ μ V n) := by
    linarith only [e1, e2]
  calc
    payoff G σ μ - payoff G π μ = _ := hdiff
    _ ≤ (1-G.discount)⁻¹ * ηminus - (1-G.discount)⁻¹ * (-ηplus) :=
      sub_le_sub hu hl
    _ = (ηplus+ηminus)/(1-G.discount) := by
      rw [div_eq_mul_inv]
      ring

noncomputable def continuationPayoff (G : Game Y A) (V : Y → ℝ)
    (y : Y) (a b : A) : ℝ :=
  G.reward y a b + G.discount * (G.physical y a b).expect V

theorem continuation_expect_eq_Q (G : Game Y A) (V : Y → ℝ) (y : Y) (a : A) :
    (G.opponent y).expect (continuationPayoff G V y a) = Q G V y a := rfl

/-- A positive affine normalization of a score transports the regret in its
original units. Constant matrices are handled without dividing by zero. -/
theorem score_regret_affine (p : Row A) (v : A → ℝ) (a : A) (l w : ℝ) :
    (l+w*v a) - p.expect (fun b => l+w*v b) =
      w*(v a-p.expect v) := by
  simp only [Row.expect_add, Row.expect_const, Row.expect_mul]
  ring

/-- Uniform continuation-game regret plus absolute evaluation residual.
The candidate can be history-dependent if both premises hold on all histories;
the pure-action upper bound is obtained at time zero for every state. -/
theorem continuation_regret_bound (G : Game Y A) (σ π : BehavioralPolicy Y A)
    (μ : Row Y) (V : Y → ℝ) {R C : ℝ}
    (hR : ∀ y a b, |G.reward y a b| ≤ R) (hC : ∀ y, |V y| ≤ C)
    (ε ρ : ℝ)
    (hreg : ∀ n hist a, Q G V (last n hist) a -
      (π n hist).expect (fun b => Q G V (last n hist) b) ≤ ε)
    (hres : ∀ n hist, |V (last n hist) -
      (π n hist).expect (fun b => Q G V (last n hist) b)| ≤ ρ) :
    payoff G σ μ - payoff G π μ ≤ (ε+2*ρ)/(1-G.discount) := by
  have h := discounted_two_residual_bound G σ π μ V hR hC (ε+ρ) ρ
    (fun y a => by
      have hr := hreg 0 y a
      have he := (abs_le.mp (hres 0 y)).1
      change Q G V y a - (π 0 y).expect (fun b => Q G V y b) ≤ ε at hr
      change -ρ ≤ V y - (π 0 y).expect (fun b => Q G V y b) at he
      linarith)
    (fun n hist => (abs_le.mp (hres n hist)).2)
  simpa only [show ε + ρ + ρ = ε + 2*ρ by ring] using h

/-- Normalized continuation regret is transported only in its original
payoff units. Width zero gives exactly zero gain, without a division. -/
theorem affine_gain_le (p : Row A) (v : A → ℝ) (a : A)
    (l w ε : ℝ) (hw : 0 ≤ w) (h : v a - p.expect v ≤ ε) :
    (l+w*v a) - p.expect (fun b => l+w*v b) ≤ w*ε := by
  rw [score_regret_affine]
  exact mul_le_mul_of_nonneg_left h hw

end PermanssonResearch.ApproxEquilibrium
