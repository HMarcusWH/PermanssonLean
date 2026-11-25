import PermanssonResearch.ApplicationBridge.PrivateStageReceipt
import Mathlib.Tactic

/-!
# Finite bimatrix regret certificates
Payoff matrices use own-action-first orientation, including the second
player's transposed matrix. Exact rational receipts are checked against all
pure deviations and transported to all real mixed deviations.
-/
namespace PermanssonResearch.ApproxEquilibrium

open ActionTrace
open scoped BigOperators
set_option autoImplicit false

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def score (R : I → J → ℝ) (q : Row J) (i : I) : ℝ :=
  q.expect (R i)

noncomputable def gain (R : I → J → ℝ) (p : Row I) (q : Row J) (i : I) : ℝ :=
  score R q i - p.expect (score R q)

/-- The payoff of every unilateral real mixed deviation is bounded. -/
def ApproxBestResponse (R : I → J → ℝ) (p : Row I) (q : Row J) (ε : ℝ) : Prop :=
  ∀ p' : Row I, p'.expect (score R q) - p.expect (score R q) ≤ ε

theorem approxBestResponse_iff_pure [DecidableEq I]
    (R : I → J → ℝ) (p : Row I) (q : Row J) (ε : ℝ) :
    ApproxBestResponse R p q ε ↔ ∀ i, gain R p q i ≤ ε := by
  constructor
  · intro h i
    simpa [gain] using h (Row.pure i)
  · intro h p'
    have hmean : p'.expect (fun i => gain R p q i) ≤ ε := by
      simpa using p'.expect_mono (g := fun _ => ε) h
    simpa [gain, Row.expect_sub] using hmean

def ApproxNash (R : I → J → ℝ) (C : J → I → ℝ)
    (p : Row I) (q : Row J) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ApproxBestResponse R p q ε ∧ ApproxBestResponse C q p ε

def rationalScore (R : I → J → ℚ) (q : J → ℚ) (i : I) : ℚ :=
  ∑ j, q j * R i j

def rationalGain (R : I → J → ℚ) (p : I → ℚ) (q : J → ℚ) (i : I) : ℚ :=
  rationalScore R q i - ∑ k, p k * rationalScore R q k

def Simplex (p : I → ℚ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

instance [DecidableEq I] (p : I → ℚ) : Decidable (Simplex p) := by
  unfold Simplex
  infer_instance

noncomputable def realRow (p : I → ℚ) (h : Simplex p) : Row I :=
  ApplicationBridge.PrivateStageReceipt.ratRow p h.1 h.2

theorem gain_eq_cast (R : I → J → ℚ) (p : I → ℚ) (q : J → ℚ)
    (hp : Simplex p) (hq : Simplex q) (i : I) :
    gain (fun k j => (R k j : ℝ)) (realRow p hp) (realRow q hq) i =
      (rationalGain R p q i : ℝ) := by
  simp [gain, score, realRow, ApplicationBridge.PrivateStageReceipt.ratRow,
    Row.expect, rationalGain, rationalScore]

/-- No guessed maximum or support is trusted. Every action is checked. -/
def NashChecks (R : I → J → ℚ) (C : J → I → ℚ)
    (p : I → ℚ) (q : J → ℚ) (ε : ℚ) : Prop :=
  Simplex p ∧ Simplex q ∧ 0 ≤ ε ∧
    (∀ i, rationalGain R p q i ≤ ε) ∧
    (∀ j, rationalGain C q p j ≤ ε)

instance [DecidableEq I] [DecidableEq J] (R : I → J → ℚ) (C : J → I → ℚ)
    (p : I → ℚ) (q : J → ℚ) (ε : ℚ) :
    Decidable (NashChecks R C p q ε) := by
  unfold NashChecks
  infer_instance

def checkNash [DecidableEq I] [DecidableEq J] (R : I → J → ℚ) (C : J → I → ℚ)
    (p : I → ℚ) (q : J → ℚ) (ε : ℚ) : Bool :=
  decide (NashChecks R C p q ε)

theorem checkNash_iff [DecidableEq I] [DecidableEq J] (R : I → J → ℚ) (C : J → I → ℚ)
    (p : I → ℚ) (q : J → ℚ) (ε : ℚ) :
    checkNash R C p q ε = true ↔ NashChecks R C p q ε := by
  simp [checkNash]

theorem rationalChecks_iff_real [DecidableEq I] [DecidableEq J]
    (R : I → J → ℚ) (C : J → I → ℚ) (p : I → ℚ) (q : J → ℚ)
    (hp : Simplex p) (hq : Simplex q) (ε : ℚ) :
    NashChecks R C p q ε ↔
      ApproxNash (fun i j => (R i j : ℝ)) (fun j i => (C j i : ℝ))
        (realRow p hp) (realRow q hq) (ε : ℝ) := by
  unfold NashChecks ApproxNash
  simp only [approxBestResponse_iff_pure]
  simp only [hp, hq, true_and]
  constructor
  · rintro ⟨he, hR, hC⟩
    refine ⟨by exact_mod_cast he, ?_, ?_⟩
    · intro i
      rw [gain_eq_cast]
      exact_mod_cast hR i
    · intro j
      rw [gain_eq_cast]
      exact_mod_cast hC j
  · rintro ⟨he, hR, hC⟩
    refine ⟨by exact_mod_cast he, ?_, ?_⟩
    · intro i
      have hi := hR i
      rw [gain_eq_cast] at hi
      exact_mod_cast hi
    · intro j
      have hj := hC j
      rw [gain_eq_cast] at hj
      exact_mod_cast hj

/-- Gap bound for a FIXED continuation score and a maximizing witness.
There is no conclusion about a simultaneous best-response fixed point. -/
theorem nonbest_mass_le (p : Row I) (v : I → ℝ) (iStar : I)
    (g ε : ℝ) (hg : 0 < g)
    (hmax : ∀ i, v i ≤ v iStar)
    (hgap : ∀ i, v i < v iStar → g ≤ v iStar - v i)
    (hregret : v iStar - p.expect v ≤ ε) :
    p.expect (fun i => if v i < v iStar then 1 else 0) ≤ ε / g := by
  classical
  have hpoint : ∀ i, g * (if v i < v iStar then 1 else 0) ≤ v iStar - v i := by
    intro i
    split_ifs with hi
    · simpa using hgap i hi
    · simpa using sub_nonneg.mpr (hmax i)
  have hmean := p.expect_mono hpoint
  rw [Row.expect_mul, Row.expect_sub, Row.expect_const] at hmean
  apply (le_div_iff₀ hg).2
  linarith

/-- An exact maximum is witnessed by an attaining action. The mask is
complete, including ties. The rational domain includes both simplex checks. -/
def ExactRegretChecks (R : I → J → ℚ) (p : I → ℚ) (q : J → ℚ)
    (r : ℚ) (best : I → Bool) : Prop :=
  Simplex p ∧ Simplex q ∧
    (∀ i, rationalGain R p q i ≤ r) ∧
    (∃ i, rationalGain R p q i = r) ∧
    (∀ i, best i = true ↔ rationalGain R p q i = r)

instance [DecidableEq I] [DecidableEq J]
    (R : I → J → ℚ) (p : I → ℚ) (q : J → ℚ) (r : ℚ) (best : I → Bool) :
    Decidable (ExactRegretChecks R p q r best) := by
  unfold ExactRegretChecks
  infer_instance

def checkExactRegret [DecidableEq I] [DecidableEq J]
    (R : I → J → ℚ) (p : I → ℚ) (q : J → ℚ) (r : ℚ) (best : I → Bool) : Bool :=
  decide (ExactRegretChecks R p q r best)

/-- Exact maximum and complete maximizing mask in the real game. -/
def ExactRegretConclusion (R : I → J → ℚ) (p : I → ℚ) (q : J → ℚ)
    (r : ℚ) (best : I → Bool) : Prop :=
  ∃ hp : Simplex p, ∃ hq : Simplex q,
    ApproxBestResponse (fun i j => (R i j : ℝ)) (realRow p hp) (realRow q hq) (r : ℝ) ∧
    (∃ p' : Row I,
      p'.expect (score (fun i j => (R i j : ℝ)) (realRow q hq)) -
        (realRow p hp).expect (score (fun i j => (R i j : ℝ)) (realRow q hq)) = (r : ℝ)) ∧
    (∀ i, best i = true ↔
      gain (fun k j => (R k j : ℝ)) (realRow p hp) (realRow q hq) i = (r : ℝ))

/-- The literal reported maximum is attained and bounds EVERY real mixed
deviation; the reported maximizing mask is exact in the same real game. -/
theorem checked_exact_regret [DecidableEq I] [DecidableEq J]
    (R : I → J → ℚ) (p : I → ℚ) (q : J → ℚ) (r : ℚ) (best : I → Bool)
    (h : checkExactRegret R p q r best = true) :
    ExactRegretConclusion R p q r best := by
  unfold ExactRegretConclusion
  have hc : ExactRegretChecks R p q r best := by
    unfold checkExactRegret at h
    exact of_decide_eq_true h
  rcases hc with ⟨hp, hq, hb, ⟨i, hi⟩, hm⟩
  refine ⟨hp, hq, ?_, ?_, ?_⟩
  · rw [approxBestResponse_iff_pure]
    intro k
    rw [gain_eq_cast]
    exact_mod_cast hb k
  · refine ⟨Row.pure i, ?_⟩
    rw [Row.expect_pure]
    change gain (fun k j => (R k j : ℝ)) (realRow p hp) (realRow q hq) i = (r : ℝ)
    rw [gain_eq_cast]
    exact_mod_cast hi
  · intro k
    rw [gain_eq_cast, hm]
    constructor
    · intro h'
      exact_mod_cast h'
    · intro h'
      exact_mod_cast h'

theorem checked_threshold_failure [DecidableEq I] [DecidableEq J]
    (R : I → J → ℚ) (C : J → I → ℚ) (p : I → ℚ) (q : J → ℚ)
    (ε : ℚ) (h : checkNash R C p q ε = false) (hp : Simplex p) (hq : Simplex q) :
    ¬ ApproxNash (fun i j => (R i j : ℝ)) (fun j i => (C j i : ℝ))
      (realRow p hp) (realRow q hq) (ε : ℝ) := by
  intro hn
  have ht := (checkNash_iff R C p q ε).2
    ((rationalChecks_iff_real R C p q hp hq ε).2 hn)
  rw [h] at ht
  contradiction

end PermanssonResearch.ApproxEquilibrium
