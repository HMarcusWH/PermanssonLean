import PermanssonResearch.Games.KiteMixing
import PermanssonResearch.Games.ApproximateDiscounted
import PermanssonResearch.X1.FullStrategyCertificate

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

def DiscountedInput.continuation (d : DiscountedInput n) (y : Fin n) (a b : Fin 2) : ℚ :=
  d.reward y a b + d.discount * ∑ z, d.physical y a b z * d.value z

def DiscountedInput.qval (d : DiscountedInput n) (y : Fin n) (a : Fin 2) : ℚ :=
  ∑ b, d.opponent y b * d.continuation y a b

def DiscountedInput.mean (d : DiscountedInput n) (y : Fin n) : ℚ :=
  ∑ a, d.own y a * d.qval y a

theorem DiscountedInput.Q_cast (d : DiscountedInput n) (y : Fin n) (a : Fin 2) :
    Q d.game (fun z => (d.value z : ℝ)) y a = (d.qval y a : ℝ) := by
  simp [Q, DiscountedInput.game, DiscountedInput.qval, DiscountedInput.continuation, realRow,
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
  have hc : DiscountedChecks d ε ρ R C := by
    unfold checkDiscounted at h
    exact of_decide_eq_true h
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

/-- One literal joint input defines both player-indexed games. Matrices
use global (row, column) action order; the second player's reward AND
controlled physical law are transposed together. -/
structure JointDiscountedInput (n : ℕ) where
  reward : Fin 2 → Fin n → Fin 2 → Fin 2 → ℚ
  physical : Fin n → Fin 2 → Fin 2 → Fin n → ℚ
  policy : Fin 2 → Fin n → Fin 2 → ℚ
  discount : Fin 2 → ℚ
  value : Fin 2 → Fin n → ℚ
  physical_ok : ∀ y a b, Simplex (physical y a b)
  policy_ok : ∀ i y, Simplex (policy i y)
  discount_ok : ∀ i, 0 ≤ discount i ∧ discount i < 1

def JointDiscountedInput.first (d : JointDiscountedInput n) : DiscountedInput n where
  player := 0
  reward := d.reward 0
  physical := d.physical
  own := d.policy 0
  opponent := d.policy 1
  discount := d.discount 0
  value := d.value 0
  physical_ok := d.physical_ok
  own_ok := d.policy_ok 0
  opponent_ok := d.policy_ok 1
  discount_ok := d.discount_ok 0

def JointDiscountedInput.second (d : JointDiscountedInput n) : DiscountedInput n where
  player := 1
  reward y a b := d.reward 1 y b a
  physical y a b := d.physical y b a
  own := d.policy 1
  opponent := d.policy 0
  discount := d.discount 1
  value := d.value 1
  physical_ok y a b := d.physical_ok y b a
  own_ok := d.policy_ok 1
  opponent_ok := d.policy_ok 0
  discount_ok := d.discount_ok 1

theorem JointDiscountedInput.same_physical (d : JointDiscountedInput n)
    (y : Fin n) (a b : Fin 2) :
    d.first.physical y a b = d.second.physical y b a := rfl

theorem JointDiscountedInput.same_profile (d : JointDiscountedInput n) :
    d.first.own = d.second.opponent ∧ d.first.opponent = d.second.own :=
  ⟨rfl, rfl⟩


/-- Source-derived two-world-state reduction of X1. The frozen 18-state
game remains authoritative; its continuation score ignores memory. -/
def x1Bool (a : Fin 2) : Bool := decide (a = 1)
def x1Fin (a : Bool) : Fin 2 := if a then 1 else 0

@[simp] theorem x1Bool_x1Fin (a : Bool) : x1Bool (x1Fin a) = a := by
  cases a <;> decide

def x1Reduced : JointDiscountedInput 2 where
  reward i s a b := PermanssonResearch.X1.reward i (x1Bool s) (x1Bool a,x1Bool b)
  physical s a b z := PermanssonResearch.X1.boolMass
    (PermanssonResearch.X1.pRep (x1Bool s) (x1Bool a,x1Bool b)) (x1Bool z)
  policy _ s a := PermanssonResearch.X1.piAction (x1Bool s) (x1Bool a)
  discount _ := PermanssonResearch.X1.discount
  value i s := PermanssonResearch.X1.value i (x1Bool s)
  physical_ok := by decide +kernel
  policy_ok := by decide +kernel
  discount_ok := by decide +kernel

theorem x1_reduced_qval :
    ∀ y a : Fin 2,
      x1Reduced.first.qval y a =
        PermanssonResearch.X1.deviationValue 0 (x1Bool y) (x1Bool a) ∧
      x1Reduced.second.qval y a =
        PermanssonResearch.X1.deviationValue 1 (x1Bool y) (x1Bool a) := by
  decide +kernel

theorem x1_reduced_actual_Q_first (m : PermanssonResearch.X1.Mode)
    (y : PermanssonResearch.X1.Y) (a : Bool) :
    Q (PermanssonResearch.X1.strategyGame m 0) (PermanssonResearch.X1.strategyValue 0) y a =
      (x1Reduced.first.qval (x1Fin y.2) (x1Fin a) : ℝ) := by
  rw [PermanssonResearch.X1.strategy_Q_eq, (x1_reduced_qval (x1Fin y.2) (x1Fin a)).1]
  simp

theorem x1_reduced_actual_Q_second (m : PermanssonResearch.X1.Mode)
    (y : PermanssonResearch.X1.Y) (a : Bool) :
    Q (PermanssonResearch.X1.strategyGame m 1) (PermanssonResearch.X1.strategyValue 1) y a =
      (x1Reduced.second.qval (x1Fin y.2) (x1Fin a) : ℝ) := by
  rw [PermanssonResearch.X1.strategy_Q_eq, (x1_reduced_qval (x1Fin y.2) (x1Fin a)).2]
  simp

theorem x1_reduced_depletion_gap :
    x1Reduced.first.qval 0 0 - x1Reduced.first.qval 0 1 = 9/211 ∧
    x1Reduced.second.qval 0 0 - x1Reduced.second.qval 0 1 = 9/211 := by
  decide +kernel

end PermanssonResearch.ApplicationBridge.EquilibriumReceipt
