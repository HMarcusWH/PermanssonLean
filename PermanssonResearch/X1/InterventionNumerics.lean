import PermanssonResearch.X1.OccupationNumerics

/-!
# Exact rational X1 intervention matrices and terminal recursion

The two protocol flags affect current action selection and next memory,
respectively. In particular, a reset never changes the current action rates.
Baseline entries reuse the same formula as `OccupationNumerics`.
-/

namespace PermanssonResearch.X1.InterventionNumerics

set_option autoImplicit false

def rates (learner restrain : Bool) (y : Y) : ℚ × ℚ :=
  if restrain then (0, 0) else OccupationNumerics.rates learner y

def next (learner reset : Bool) (y : Y) (a : Action) : Memory :=
  if reset then (1, 1) else OccupationNumerics.next learner y a

def entry (learner restrain reset : Bool) (y z : Y) : ℚ :=
  ∑ a : Action, boolMass (rates learner restrain y).1 a.1 *
    boolMass (rates learner restrain y).2 a.2 * boolMass (pRep y.2 a) z.2 *
      if next learner reset y a = z.1 then 1 else 0

theorem baseline_entry (learner : Bool) (y z : Y) :
    entry learner false false y z = OccupationNumerics.entry learner y z := rfl

/-- An elementary presentation of reinforcement, certified against the actual
old-world payoff/sign/clipping definition rather than substituted for it. -/
def elementaryUpdate (y : Y) (a : Action) : Memory :=
  if y.2 then
    if a.1 && a.2 then
      (clipMemory ((y.1.1.val : ℤ) - 1), clipMemory ((y.1.2.val : ℤ) - 1))
    else (clipMemory ((y.1.1.val : ℤ) + 1), clipMemory ((y.1.2.val : ℤ) + 1))
  else
    (clipMemory ((y.1.1.val : ℤ) + 1 - 2 * (if a.1 then 1 else 0)),
      clipMemory ((y.1.2.val : ℤ) + 1 - 2 * (if a.2 then 1 else 0)))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem elementaryUpdate_eq_updateL : ∀ (y : Y) (a : Action),
    elementaryUpdate y a = updateL y a := by
  decide +kernel

theorem rates_bounds (learner restrain : Bool) (y : Y) :
    (0 ≤ (rates learner restrain y).1 ∧ (rates learner restrain y).1 ≤ 1) ∧
      (0 ≤ (rates learner restrain y).2 ∧ (rates learner restrain y).2 ≤ 1) := by
  cases restrain <;> cases learner
  · exact ⟨piExtract_bounds _, piExtract_bounds _⟩
  · exact ⟨learnerExtract_bounds _, learnerExtract_bounds _⟩
  all_goals norm_num [rates]

theorem mass_nonneg (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (b : Bool) : 0 ≤ boolMass p b := by
  cases b with
  | false => exact sub_nonneg.mpr hp.2
  | true => exact hp.1

theorem entry_nonneg (learner restrain reset : Bool) (y z : Y) :
    0 ≤ entry learner restrain reset y z := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg (mass_nonneg _ (rates_bounds learner restrain y).1 _)
      (mass_nonneg _ (rates_bounds learner restrain y).2 _))
      (mass_nonneg _ (pRep_bounds y.2 a) _)
  · split_ifs <;> norm_num

theorem world_row (p : ℚ) (q : Memory) :
    (∑ z : Y, boolMass p z.2 * if q = z.1 then 1 else 0) = 1 := by
  rcases q with ⟨q₁,q₂⟩
  simp [Fintype.sum_prod_type, sum_bool, boolMass, mul_ite]

theorem entry_sum_one (learner restrain reset : Bool) (y : Y) :
    (∑ z : Y, entry learner restrain reset y z) = 1 := by
  unfold entry
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, world_row, mul_one]
  simp [Fintype.sum_prod_type, sum_bool, boolMass]
  ring

/-- Terminal repletion, allowing exits and re-entry at intermediate times. -/
def terminal (learner restrain reset : Bool) : ℕ → Y → ℚ
  | 0, y => indicator y.2
  | n+1, y => ∑ z : Y, entry learner restrain reset y z *
      terminal learner restrain reset n z

theorem terminal_bounds (learner restrain reset : Bool) (n : ℕ) (y : Y) :
    0 ≤ terminal learner restrain reset n y ∧
      terminal learner restrain reset n y ≤ 1 := by
  induction n generalizing y with
  | zero => rcases y with ⟨q,x⟩; cases x <;> norm_num [terminal, indicator]
  | succ n ih =>
      constructor
      · exact Finset.sum_nonneg fun z _ =>
          mul_nonneg (entry_nonneg learner restrain reset y z) (ih z).1
      · calc
          _ ≤ ∑ z : Y, entry learner restrain reset y z * 1 :=
            Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (ih z).2
              (entry_nonneg learner restrain reset y z)
          _ = 1 := by simpa only [mul_one] using entry_sum_one learner restrain reset y

end PermanssonResearch.X1.InterventionNumerics
