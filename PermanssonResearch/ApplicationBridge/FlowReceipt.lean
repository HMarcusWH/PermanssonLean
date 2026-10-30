import PermanssonResearch.ApplicationBridge.ControlTableReceipt
import PermanssonResearch.ReverseSolver.C11TypedStationaryBridge
import Mathlib.Tactic

/-!
# ApplicationBridge — one-step risk-constrained occupancy (flow) receipts

From an initial law `μ`, a fully observed randomized Markov policy `π` over
the declared feasible actions induces the one-step next-state law
`ν z = Σ_y Σ_a μ y π y a K_a(y, z)`, where `K_a` is the fixed-action P·U row
of the reflected source. A flow receipt reports an occupancy `q y a`, a dual
certificate (`v` for the mass equalities, `λ ≥ 0` for the risk cap, `w ≥ 0`
for the bounds `q ≤ μ`), the optimum `D`, and the reconstructed policy.

`checked_risk_optimum`: every admissible **real** randomized policy whose
next-step risk mass is within the cap has expected terminal reward at most
`D`, and the reconstructed policy attains `D` within the cap. The certificate
is checked, not assumed equal to any solver output. One transition only; no
multi-stage occupancy, private-information or robust statement.
-/

open MeasureTheory

namespace PermanssonResearch.ApplicationBridge.FlowReceipt

open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonResearch.ReverseSolver.C11

set_option autoImplicit false

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

variable {N na : ℕ}

def rewardCoeff (rows : Fin na → RationalMarkovMatrix N) (r : Fin N → ℚ) (y : Fin N)
    (a : Fin na) : ℚ :=
  ∑ z, (rows a).entry y z * r z

def riskCoeff (rows : Fin na → RationalMarkovMatrix N) (risk : Finset (Fin N)) (y : Fin N)
    (a : Fin na) : ℚ :=
  ∑ z ∈ risk, (rows a).entry y z

/-- One-step next-state law of a real randomized Markov policy from `μ`. -/
noncomputable def nextLaw (rows : Fin na → RationalMarkovMatrix N) (μ : Fin N → ℚ)
    (π : Fin N → Fin na → ℝ) (z : Fin N) : ℝ :=
  ∑ y, ∑ a, (μ y : ℝ) * π y a * ((rows a).entry y z : ℝ)

noncomputable def expectedReward (rows : Fin na → RationalMarkovMatrix N) (μ r : Fin N → ℚ)
    (π : Fin N → Fin na → ℝ) : ℝ :=
  ∑ z, nextLaw rows μ π z * (r z : ℝ)

noncomputable def riskMass (rows : Fin na → RationalMarkovMatrix N) (μ : Fin N → ℚ)
    (risk : Finset (Fin N)) (π : Fin N → Fin na → ℝ) : ℝ :=
  ∑ z ∈ risk, nextLaw rows μ π z

/-- A probability over the admitted actions at every state. -/
def Admissible (options : Fin N → Finset (Fin na)) (π : Fin N → Fin na → ℝ) : Prop :=
  (∀ y a, 0 ≤ π y a) ∧ (∀ y, ∑ a, π y a = 1) ∧ (∀ y a, a ∉ options y → π y a = 0)

theorem expectedReward_eq (rows : Fin na → RationalMarkovMatrix N) (μ r : Fin N → ℚ)
    (π : Fin N → Fin na → ℝ) :
    expectedReward rows μ r π =
      ∑ y, ∑ a, (μ y : ℝ) * π y a * (rewardCoeff rows r y a : ℝ) := by
  unfold expectedReward nextLaw rewardCoeff
  push_cast
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem riskMass_eq (rows : Fin na → RationalMarkovMatrix N) (μ : Fin N → ℚ)
    (risk : Finset (Fin N)) (π : Fin N → Fin na → ℝ) :
    riskMass rows μ risk π =
      ∑ y, ∑ a, (μ y : ℝ) * π y a * (riskCoeff rows risk y a : ℝ) := by
  unfold riskMass nextLaw riskCoeff
  push_cast
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]

/-- Primal flow feasibility and value, dual feasibility and bound, and the
    reconstructed policy. -/
def FlowChecks (rows : Fin na → RationalMarkovMatrix N) (options : Fin N → Finset (Fin na))
    (μ r : Fin N → ℚ) (risk : Finset (Fin N)) (cap : ℚ) (q : Fin N → Fin na → ℚ)
    (v : Fin N → ℚ) (lam : ℚ) (wB : Fin N → Fin na → ℚ) (D : ℚ)
    (πr : Fin N → Fin na → ℚ) : Prop :=
  (∀ y a, 0 ≤ q y a) ∧ (∀ y a, a ∉ options y → q y a = 0) ∧ (∀ y, ∑ a, q y a = μ y) ∧
  (∑ y, ∑ a, q y a * riskCoeff rows risk y a) ≤ cap ∧
  (∑ y, ∑ a, q y a * rewardCoeff rows r y a) = D ∧
  0 ≤ lam ∧ (∀ y a, 0 ≤ wB y a) ∧
  (∀ y, ∀ a ∈ options y, rewardCoeff rows r y a ≤ v y + lam * riskCoeff rows risk y a + wB y a) ∧
  D = (∑ y, v y * μ y) + lam * cap + ∑ y, ∑ a, wB y a * μ y ∧
  (∀ y, 0 ≤ μ y) ∧
  (∀ y a, 0 ≤ πr y a) ∧ (∀ y, ∑ a, πr y a = 1) ∧ (∀ y a, a ∉ options y → πr y a = 0) ∧
  (∀ y a, μ y * πr y a = q y a)

instance (rows : Fin na → RationalMarkovMatrix N) (options : Fin N → Finset (Fin na))
    (μ r : Fin N → ℚ) (risk : Finset (Fin N)) (cap : ℚ) (q : Fin N → Fin na → ℚ)
    (v : Fin N → ℚ) (lam : ℚ) (wB : Fin N → Fin na → ℚ) (D : ℚ) (πr : Fin N → Fin na → ℚ) :
    Decidable (FlowChecks rows options μ r risk cap q v lam wB D πr) := by
  unfold FlowChecks
  infer_instance

def checkFlowReceipt (rows : Fin na → RationalMarkovMatrix N) (options : Fin N → Finset (Fin na))
    (μ r : Fin N → ℚ) (risk : Finset (Fin N)) (cap : ℚ) (q : Fin N → Fin na → ℚ)
    (v : Fin N → ℚ) (lam : ℚ) (wB : Fin N → Fin na → ℚ) (D : ℚ)
    (πr : Fin N → Fin na → ℚ) : Bool :=
  decide (FlowChecks rows options μ r risk cap q v lam wB D πr)

theorem checkFlowReceipt_sound (rows : Fin na → RationalMarkovMatrix N)
    (options : Fin N → Finset (Fin na)) (μ r : Fin N → ℚ) (risk : Finset (Fin N)) (cap : ℚ)
    (q : Fin N → Fin na → ℚ) (v : Fin N → ℚ) (lam : ℚ) (wB : Fin N → Fin na → ℚ) (D : ℚ)
    (πr : Fin N → Fin na → ℚ)
    (h : checkFlowReceipt rows options μ r risk cap q v lam wB D πr = true) :
    FlowChecks rows options μ r risk cap q v lam wB D πr := by
  unfold checkFlowReceipt at h
  exact of_decide_eq_true h

section Receipt

variable (rows : Fin na → RationalMarkovMatrix N) (options : Fin N → Finset (Fin na))
  (μ r : Fin N → ℚ) (risk : Finset (Fin N)) (cap : ℚ) (q : Fin N → Fin na → ℚ)
  (v : Fin N → ℚ) (lam : ℚ) (wB : Fin N → Fin na → ℚ) (D : ℚ) (πr : Fin N → Fin na → ℚ)
  (h : checkFlowReceipt rows options μ r risk cap q v lam wB D πr = true)
include h

/-- The reconstructed policy as a real policy. -/
def realPolicy : Fin N → Fin na → ℝ := fun y a => (πr y a : ℝ)

/-- Optimality over every admissible real randomized one-step policy within
    the risk cap, attained by the reconstructed policy. -/
theorem checked_risk_optimum :
    (∀ π : Fin N → Fin na → ℝ, Admissible options π → riskMass rows μ risk π ≤ cap →
      expectedReward rows μ r π ≤ D) ∧
    Admissible options (realPolicy πr) ∧
    expectedReward rows μ r (realPolicy πr) = D ∧ riskMass rows μ risk (realPolicy πr) ≤ cap := by
  obtain ⟨-, -, -, hqrisk, hqval, hlam, hw, hdual, hD, hμ, hπ0, hπ1, hπopt, hrec⟩ :=
    checkFlowReceipt_sound rows options μ r risk cap q v lam wB D πr h
  have hrecR : ∀ y a, (μ y : ℝ) * (πr y a : ℝ) = (q y a : ℝ) := fun y a => by
    exact_mod_cast hrec y a
  refine ⟨fun π hadm hrisk => ?_, ⟨fun y a => by unfold realPolicy; exact_mod_cast hπ0 y a,
    fun y => by unfold realPolicy; exact_mod_cast hπ1 y,
    fun y a ha => by simp [realPolicy, hπopt y a ha]⟩, ?_, ?_⟩
  · obtain ⟨hp0, hp1, hpopt⟩ := hadm
    rw [expectedReward_eq]
    have hterm : ∀ y a, (μ y : ℝ) * π y a * (rewardCoeff rows r y a : ℝ) ≤
        (μ y : ℝ) * π y a * ((v y : ℝ) + (lam : ℝ) * (riskCoeff rows risk y a : ℝ) +
          (wB y a : ℝ)) := by
      intro y a
      by_cases ha : a ∈ options y
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by exact_mod_cast hμ y) (hp0 y a))
        exact_mod_cast hdual y a ha
      · simp [hpopt y a ha]
    have hle_one : ∀ y a, π y a ≤ 1 := by
      intro y a
      rw [← hp1 y]
      exact Finset.single_le_sum (fun b _ => hp0 y b) (Finset.mem_univ a)
    calc ∑ y, ∑ a, (μ y : ℝ) * π y a * (rewardCoeff rows r y a : ℝ)
        ≤ ∑ y, ∑ a, (μ y : ℝ) * π y a * ((v y : ℝ) + (lam : ℝ) * (riskCoeff rows risk y a : ℝ) +
            (wB y a : ℝ)) :=
          Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun a _ => hterm y a))
      _ = (∑ y, (v y : ℝ) * (μ y : ℝ)) + (lam : ℝ) * riskMass rows μ risk π +
            ∑ y, ∑ a, (μ y : ℝ) * π y a * (wB y a : ℝ) := by
          rw [riskMass_eq, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro y _
          have hsum : ∑ a, (μ y : ℝ) * π y a * (v y : ℝ) = (v y : ℝ) * (μ y : ℝ) := by
            rw [← Finset.sum_mul, ← Finset.mul_sum, hp1 y]
            ring
          rw [Finset.mul_sum, ← hsum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring
      _ ≤ (∑ y, (v y : ℝ) * (μ y : ℝ)) + (lam : ℝ) * (cap : ℝ) +
            ∑ y, ∑ a, (wB y a : ℝ) * (μ y : ℝ) := by
          have hl : (0 : ℝ) ≤ lam := by exact_mod_cast hlam
          have h1 : (lam : ℝ) * riskMass rows μ risk π ≤ (lam : ℝ) * (cap : ℝ) :=
            mul_le_mul_of_nonneg_left hrisk hl
          have h2 : ∑ y, ∑ a, (μ y : ℝ) * π y a * (wB y a : ℝ) ≤
              ∑ y, ∑ a, (wB y a : ℝ) * (μ y : ℝ) := by
            apply Finset.sum_le_sum
            intro y _
            apply Finset.sum_le_sum
            intro a _
            have hw0 : (0 : ℝ) ≤ wB y a := by exact_mod_cast hw y a
            have hμ0 : (0 : ℝ) ≤ μ y := by exact_mod_cast hμ y
            nlinarith [hle_one y a, hp0 y a, mul_nonneg hw0 hμ0]
          linarith
      _ = (D : ℝ) := by
          rw [hD]
          push_cast
          ring
  · rw [expectedReward_eq, ← hqval]
    push_cast
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro a _
    unfold realPolicy
    rw [hrecR y a]
  · rw [riskMass_eq]
    have hcast : (∑ y, ∑ a, ((q y a * riskCoeff rows risk y a : ℚ) : ℝ)) ≤ (cap : ℝ) := by
      exact_mod_cast hqrisk
    calc ∑ y, ∑ a, (μ y : ℝ) * realPolicy πr y a * (riskCoeff rows risk y a : ℝ)
        = ∑ y, ∑ a, ((q y a * riskCoeff rows risk y a : ℚ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro y _
          apply Finset.sum_congr rfl
          intro a _
          unfold realPolicy
          push_cast
          rw [hrecR y a]
      _ ≤ (cap : ℝ) := hcast

end Receipt

/-- One-step atoms of a realized matrix are its entries. -/
theorem realized_one_step_atom {n : ℕ} (M : RationalMarkovMatrix n) (y z : Fin n) :
    ((realizedModel M).inducedKernel (decode y)).real {decode z} = (M.entry y z : ℝ) :=
  typed_realTransition_eq M y z

end PermanssonResearch.ApplicationBridge.FlowReceipt
