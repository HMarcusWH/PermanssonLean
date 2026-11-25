import PermanssonResearch.Games.BimatrixRegret
import PermanssonResearch.Games.ApproximateDiscounted

/-! A literal rational receipt checks every action before it is interpreted as
a real mixed-deviation bound. No external solver flag is a theorem premise. -/
namespace PermanssonResearch.ApplicationBridge.EquilibriumReceipt

open ApproxEquilibrium ActionTrace DiscountedVerification
open scoped BigOperators
set_option autoImplicit false

theorem checked_profile {m n : ℕ}
    (R : Fin m → Fin n → ℚ) (C : Fin n → Fin m → ℚ)
    (p : Fin m → ℚ) (q : Fin n → ℚ) (ε : ℚ)
    (h : checkNash R C p q ε = true) :
    ∃ hp : Simplex p, ∃ hq : Simplex q,
      ApproxNash (fun i j => (R i j : ℝ)) (fun j i => (C j i : ℝ))
        (realRow p hp) (realRow q hq) (ε : ℝ) := by
  have hc := (checkNash_iff R C p q ε).1 h
  exact ⟨hc.1, hc.2.1, (rationalChecks_iff_real R C p q hc.1 hc.2.1 ε).1 hc⟩

/-- Literal rational input for one indexed player, own-action-first.
The opponent and controlled state transition are fixed under every deviation. -/
structure DiscountedInput (n : ℕ) where
  player : Fin 2
  reward : Fin n → Fin 2 → Fin 2 → ℚ
  physical : Fin n → Fin 2 → Fin 2 → Fin n → ℚ
  own : Fin n → Fin 2 → ℚ
  opponent : Fin n → Fin 2 → ℚ
  discount : ℚ
  value : Fin n → ℚ
  physical_ok : ∀ y a b, Simplex (physical y a b)
  own_ok : ∀ y, Simplex (own y)
  opponent_ok : ∀ y, Simplex (opponent y)
  discount_ok : 0 ≤ discount ∧ discount < 1

variable {n : ℕ}

noncomputable def DiscountedInput.game (d : DiscountedInput n) : Game (Fin n) (Fin 2) where
  player := d.player
  reward y a b := d.reward y a b
  physical y a b := realRow (d.physical y a b) (d.physical_ok y a b)
  opponent y := realRow (d.opponent y) (d.opponent_ok y)
  discount := d.discount
  discount_nonneg := by exact_mod_cast d.discount_ok.1
  discount_lt_one := by exact_mod_cast d.discount_ok.2

noncomputable def DiscountedInput.policy (d : DiscountedInput n) :
    BehavioralPolicy (Fin n) (Fin 2) :=
  fun t hist => realRow (d.own (last t hist)) (d.own_ok (last t hist))

def DiscountedInput.qval (d : DiscountedInput n) (y : Fin n) (a : Fin 2) : ℚ :=
  ∑ b, d.opponent y b * (d.reward y a b +
    d.discount * ∑ z, d.physical y a b z * d.value z)

def DiscountedInput.mean (d : DiscountedInput n) (y : Fin n) : ℚ :=
  ∑ a, d.own y a * d.qval y a

theorem DiscountedInput.Q_cast (d : DiscountedInput n) (y : Fin n) (a : Fin 2) :
    Q d.game (fun z => (d.value z : ℝ)) y a = (d.qval y a : ℝ) := by
  simp [Q, DiscountedInput.game, DiscountedInput.qval, realRow,
    ApplicationBridge.PrivateStageReceipt.ratRow, Row.expect]

theorem DiscountedInput.mean_cast (d : DiscountedInput n) (t : ℕ)
    (hist : History (Fin n) (Fin 2 × Fin 2) t) :
    (d.policy t hist).expect (fun a => Q d.game (fun z => (d.value z : ℝ)) (last t hist) a) =
      (d.mean (last t hist) : ℝ) := by
  simp [DiscountedInput.policy, DiscountedInput.mean, DiscountedInput.Q_cast,
    realRow, ApplicationBridge.PrivateStageReceipt.ratRow, Row.expect]

/-- All state/action inequalities and both signs of the evaluation residual
are checked. R and C are explicit absolute bounds on rewards and values. -/
def DiscountedChecks (d : DiscountedInput n) (ε ρ R C : ℚ) : Prop :=
  0 ≤ ε ∧ 0 ≤ ρ ∧
  (∀ y a b, |d.reward y a b| ≤ R) ∧
  (∀ y, |d.value y| ≤ C) ∧
  (∀ y a, d.qval y a - d.mean y ≤ ε) ∧
  (∀ y, |d.value y - d.mean y| ≤ ρ)

instance (d : DiscountedInput n) (ε ρ R C : ℚ) :
    Decidable (DiscountedChecks d ε ρ R C) := by
  unfold DiscountedChecks
  infer_instance

def checkDiscounted (d : DiscountedInput n) (ε ρ R C : ℚ) : Bool :=
  decide (DiscountedChecks d ε ρ R C)

/-- Literal rational checks imply a full-history guarantee in the actual
ActionTrace game assembled from those rows and values. -/
theorem checked_discounted (d : DiscountedInput n) (ε ρ R C : ℚ)
    (h : checkDiscounted d ε ρ R C = true)
    (σ : BehavioralPolicy (Fin n) (Fin 2)) (μ : Row (Fin n)) :
    payoff d.game σ μ - payoff d.game d.policy μ ≤
      ((ε:ℝ)+2*(ρ:ℝ))/(1-d.game.discount) := by
  have hc : DiscountedChecks d ε ρ R C := of_decide_eq_true h
  rcases hc with ⟨he,hr,hR,hC,hreg,hres⟩
  apply continuation_regret_bound d.game σ d.policy μ (fun y => (d.value y : ℝ))
    (R := (R:ℝ)) (C := (C:ℝ))
  · intro y a b
    change |(d.reward y a b : ℝ)| ≤ (R:ℝ)
    exact_mod_cast hR y a b
  · intro y
    exact_mod_cast hC y
  · intro t hist a
    rw [d.Q_cast, d.mean_cast]
    exact_mod_cast hreg (last t hist) a
  · intro t hist
    rw [d.mean_cast]
    exact_mod_cast hres (last t hist)

end PermanssonResearch.ApplicationBridge.EquilibriumReceipt
