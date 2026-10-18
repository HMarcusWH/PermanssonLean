import PermanssonResearch.StrategicWorld.ActionTraceCanonical
import PermanssonResearch.Games.DiscountedVerification
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Expected path sums agree with the scalar action-trace payoff. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace PermanssonResearch.DiscountedVerification

open ActionTrace
set_option autoImplicit false
universe u
variable {Y A : Type u} [Fintype Y] [Fintype A]
  [MeasurableSpace Y] [MeasurableSpace A]
  [DiscreteMeasurableSpace Y] [DiscreteMeasurableSpace A]

/-- Stage reward reads the recorded action at time n from history n+1. -/
def pathReward (G : Game Y A) (n : ℕ) (w : (t : ℕ) → History Y (A × A) t) : ℝ :=
  G.reward (last n (w (n+1)).1) (w (n+1)).2.1.1 (w (n+1)).2.1.2

theorem integral_pathReward (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y) (n : ℕ) :
    (∫ w, pathReward G n w ∂canonicalLaw G σ μ) = stageReward G σ μ n := by
  simpa only [pathReward, stageReward] using canonical_expect G σ μ (n+1)
    (fun h => G.reward (last n h.1) h.2.1.1 h.2.1.2)

theorem measurable_pathReward (G : Game Y A) (n : ℕ) : Measurable (pathReward G n) := by
  have hm : Measurable (fun h : History Y (A × A) (n+1) =>
      G.reward (last n h.1) h.2.1.1 h.2.1.2) := Measurable.of_discrete
  exact hm.comp (measurable_pi_apply (n+1))

theorem pathReward_abs_le (G : Game Y A) {R : ℝ}
    (hR : ∀ y a b, |G.reward y a b| ≤ R) (n : ℕ)
    (w : (t : ℕ) → History Y (A × A) t) : |pathReward G n w| ≤ R := hR _ _ _

theorem path_reward_summable (G : Game Y A) {R : ℝ}
    (hR : ∀ y a b, |G.reward y a b| ≤ R)
    (w : (t : ℕ) → History Y (A × A) t) :
    Summable (fun n => G.discount^n * pathReward G n w) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one G.discount_nonneg G.discount_lt_one).mul_right R)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg G.discount_nonneg _)]
  exact mul_le_mul_of_nonneg_left (pathReward_abs_le G hR n w)
    (pow_nonneg G.discount_nonneg _)

/-- Expectation of the absolutely convergent discounted reward on the genuine
canonical trace space equals the scalar series used by verification. -/
theorem payoff_eq_expected_path_sum (G : Game Y A) (σ : BehavioralPolicy Y A) (μ : Row Y)
    {R : ℝ} (hR : ∀ y a b, |G.reward y a b| ≤ R) :
    payoff G σ μ = ∫ w, (∑' n, G.discount^n * pathReward G n w)
      ∂canonicalLaw G σ μ := by
  have hint (n : ℕ) : Integrable (fun w => G.discount^n * pathReward G n w)
      (canonicalLaw G σ μ) := by
    apply Integrable.mono' (integrable_const (G.discount^n * R))
      ((measurable_pathReward G n).const_mul _).aestronglyMeasurable
    apply ae_of_all
    intro w
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg G.discount_nonneg _)]
    exact mul_le_mul_of_nonneg_left (pathReward_abs_le G hR n w)
      (pow_nonneg G.discount_nonneg _)
  have hnorm (n : ℕ) : (∫ w, ‖G.discount^n * pathReward G n w‖
      ∂canonicalLaw G σ μ) ≤ G.discount^n * R := by
    calc
      _ ≤ ∫ _w, G.discount^n * R ∂canonicalLaw G σ μ := by
        apply integral_mono (hint n).norm (integrable_const _)
        intro w
        change ‖G.discount^n * pathReward G n w‖ ≤ G.discount^n * R
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg G.discount_nonneg _)]
        exact mul_le_mul_of_nonneg_left (pathReward_abs_le G hR n w)
          (pow_nonneg G.discount_nonneg _)
      _ = _ := by simp
  have hs : Summable (fun n => ∫ w, ‖G.discount^n * pathReward G n w‖
      ∂canonicalLaw G σ μ) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
      hnorm ((summable_geometric_of_lt_one G.discount_nonneg G.discount_lt_one).mul_right R)
  rw [← integral_tsum_of_summable_integral_norm hint hs]
  simp only [integral_const_mul, integral_pathReward, payoff]

/-- The exported verification statement is about expected discounted reward on
an actual action-retaining infinite probability space. -/
theorem expected_discounted_verification (G : Game Y A) (σ : BehavioralPolicy Y A)
    (μ : Row Y) (V : Y → ℝ) {R C : ℝ}
    (hR : ∀ y a b, |G.reward y a b| ≤ R) (hC : ∀ y, |V y| ≤ C)
    (hV : ∀ y a, Q G V y a ≤ V y) :
    (∫ w, (∑' n, G.discount^n * pathReward G n w) ∂canonicalLaw G σ μ) ≤
      μ.expect V := by
  rw [← payoff_eq_expected_path_sum G σ μ hR]
  exact discounted_verification G σ μ V hR hC hV

end PermanssonResearch.DiscountedVerification
