import PermanssonResearch.ApplicationBridge.FlowReceipt
import Mathlib.Tactic

/-!
# ApplicationBridge — one-step risk-cap infeasibility receipts

For the one-step risk problem of `FlowReceipt`, a fully observed randomized
Markov policy `π` over the admitted actions puts risk mass
`Σ_y Σ_a μ y π y a riskCoeff(y, a)` on the risk set. An infeasibility receipt
reports one floor `v y` per state. `FloorChecks` decides that `μ ≥ 0`, that
every admitted action at `y` has risk coefficient at least `v y`, that some
admitted action attains `v y`, and that `cap < Σ_y v y μ y`. The floors are
the normalized Farkas ray of the occupancy program: risk-cap multiplier one
and mass multipliers `v`.

`checked_min_risk` states that `Σ_y v y μ y` is the least risk mass of any
admissible real randomized policy, attained by a pure policy.
`checked_cap_infeasible` states that every admissible real randomized policy
exceeds the cap, so no policy meets it. One transition only. The bounded
LP generator of the optimum route is not involved.
-/

namespace PermanssonResearch.ApplicationBridge.FlowInfeasibilityReceipt

open PermanssonResearch.ReverseSolver
open PermanssonResearch.ApplicationBridge.FlowReceipt

set_option autoImplicit false

variable {N na : ℕ}

/-- Per-state risk floors over the admitted actions, attained, and above the cap in total. -/
def FloorChecks (rows : Fin na → RationalMarkovMatrix N) (options : Fin N → Finset (Fin na))
    (μ : Fin N → ℚ) (risk : Finset (Fin N)) (cap : ℚ) (v : Fin N → ℚ) : Prop :=
  (∀ y, 0 ≤ μ y) ∧ (∀ y, ∀ a ∈ options y, v y ≤ riskCoeff rows risk y a) ∧
  (∀ y, ∃ a ∈ options y, riskCoeff rows risk y a = v y) ∧ cap < ∑ y, v y * μ y

instance (rows : Fin na → RationalMarkovMatrix N) (options : Fin N → Finset (Fin na))
    (μ : Fin N → ℚ) (risk : Finset (Fin N)) (cap : ℚ) (v : Fin N → ℚ) :
    Decidable (FloorChecks rows options μ risk cap v) := by
  unfold FloorChecks
  infer_instance

def checkRiskFloors (rows : Fin na → RationalMarkovMatrix N) (options : Fin N → Finset (Fin na))
    (μ : Fin N → ℚ) (risk : Finset (Fin N)) (cap : ℚ) (v : Fin N → ℚ) : Bool :=
  decide (FloorChecks rows options μ risk cap v)

theorem checkRiskFloors_sound (rows : Fin na → RationalMarkovMatrix N)
    (options : Fin N → Finset (Fin na)) (μ : Fin N → ℚ) (risk : Finset (Fin N)) (cap : ℚ)
    (v : Fin N → ℚ) (h : checkRiskFloors rows options μ risk cap v = true) :
    FloorChecks rows options μ risk cap v := by
  unfold checkRiskFloors at h
  exact of_decide_eq_true h

section Receipt

variable (rows : Fin na → RationalMarkovMatrix N) (options : Fin N → Finset (Fin na))
  (μ : Fin N → ℚ) (risk : Finset (Fin N)) (cap : ℚ) (v : Fin N → ℚ)
  (h : checkRiskFloors rows options μ risk cap v = true)
include h

theorem floor_le_riskMass (π : Fin N → Fin na → ℝ) (hπ : Admissible options π) :
    ((∑ y, v y * μ y : ℚ) : ℝ) ≤ riskMass rows μ risk π := by
  obtain ⟨hμ, hfloor, -, -⟩ := checkRiskFloors_sound rows options μ risk cap v h
  obtain ⟨hp0, hp1, hpopt⟩ := hπ
  rw [riskMass_eq]
  push_cast
  apply Finset.sum_le_sum
  intro y _
  calc (v y : ℝ) * (μ y : ℝ) = ∑ a, (μ y : ℝ) * π y a * (v y : ℝ) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, hp1 y]
        ring
    _ ≤ ∑ a, (μ y : ℝ) * π y a * (riskCoeff rows risk y a : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : a ∈ options y
        · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hfloor y a ha)
            (mul_nonneg (by exact_mod_cast hμ y) (hp0 y a))
        · simp [hpopt y a ha]

/-- The least risk mass of any admissible real randomized policy is the
    floor total, attained by a pure policy. -/
theorem checked_min_risk :
    (∀ π : Fin N → Fin na → ℝ, Admissible options π →
      ((∑ y, v y * μ y : ℚ) : ℝ) ≤ riskMass rows μ risk π) ∧
    ∃ π : Fin N → Fin na → ℝ, Admissible options π ∧
      riskMass rows μ risk π = ((∑ y, v y * μ y : ℚ) : ℝ) := by
  obtain ⟨-, -, hattain, -⟩ := checkRiskFloors_sound rows options μ risk cap v h
  choose f hf using hattain
  refine ⟨fun π hπ => floor_le_riskMass rows options μ risk cap v h π hπ,
    fun y a => if a = f y then 1 else 0, ⟨fun y a => by dsimp only; split_ifs <;> norm_num,
      fun y => by simp, fun y a ha => ?_⟩, ?_⟩
  · have hne : a ≠ f y := fun he => ha (he ▸ (hf y).1)
    simp [hne]
  · rw [riskMass_eq]
    push_cast
    apply Finset.sum_congr rfl
    intro y _
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte]
    rw [(hf y).2, mul_comm]

/-- Every admissible real randomized policy exceeds the cap: no policy meets it. -/
theorem checked_cap_infeasible :
    (∀ π : Fin N → Fin na → ℝ, Admissible options π → (cap : ℝ) < riskMass rows μ risk π) ∧
    ¬ ∃ π : Fin N → Fin na → ℝ, Admissible options π ∧ riskMass rows μ risk π ≤ cap := by
  obtain ⟨-, -, -, hcap⟩ := checkRiskFloors_sound rows options μ risk cap v h
  have hlt : ∀ π : Fin N → Fin na → ℝ, Admissible options π → (cap : ℝ) < riskMass rows μ risk π :=
    fun π hπ => lt_of_lt_of_le (by exact_mod_cast hcap) (floor_le_riskMass rows options μ risk cap v h π hπ)
  exact ⟨hlt, fun ⟨π, hπ, hle⟩ => absurd hle (not_le.mpr (hlt π hπ))⟩

end Receipt

end PermanssonResearch.ApplicationBridge.FlowInfeasibilityReceipt
