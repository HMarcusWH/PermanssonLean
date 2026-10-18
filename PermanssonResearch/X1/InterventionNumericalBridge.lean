import PermanssonResearch.X1.InterventionNumerics
import PermanssonResearch.X1.OccupationTargets
import PermanssonResearch.X1.FiniteOutputs

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace PermanssonResearch.X1

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

/-- The unique exhaustive flag-to-existing-model mapping. -/
noncomputable def protocolModel (m : Mode) : Bool → Bool →
    StrategicWorldModel Memory Bool Action
  | false, false => model m
  | true, false => (Jaction m).intervention.apply
  | false, true => (Jupdate m).intervention.apply
  | true, true => (Jjoint m).intervention.apply

theorem protocolModel_action (m : Mode) (r u : Bool) :
    (protocolModel m r u).generator.action = if r then restrainAction else action m := by
  cases r <;> cases u <;> rfl

theorem protocolModel_update (m : Mode) (r u : Bool) :
    (protocolModel m r u).generator.update = if u then resetUpdate else update m := by
  cases r <;> cases u <;> rfl

theorem protocolModel_world (m : Mode) (r u : Bool) :
    (protocolModel m r u).world = world := by
  cases r <;> cases u <;> rfl

theorem protocol_rates_bounds (m : Mode) (r : Bool) (y : Y) :
    (0 ≤ (InterventionNumerics.rates (learnerFlag m) r y).1 ∧
      (InterventionNumerics.rates (learnerFlag m) r y).1 ≤ 1) ∧
    (0 ≤ (InterventionNumerics.rates (learnerFlag m) r y).2 ∧
      (InterventionNumerics.rates (learnerFlag m) r y).2 ≤ 1) := by
  cases r with
  | false => simpa [InterventionNumerics.rates, numerical_rates_eq] using extractionRate_bounds m y
  | true => norm_num [InterventionNumerics.rates]

theorem protocol_action_lintegral (m : Mode) (r u : Bool) (y : Y)
    (f : Action → ℝ≥0∞) :
    (∫⁻ a, f a ∂(protocolModel m r u).generator.action y) =
      ∑ a : Action,
        ENNReal.ofReal (boolMass (InterventionNumerics.rates (learnerFlag m) r y).1 a.1 : ℝ) *
        ENNReal.ofReal (boolMass (InterventionNumerics.rates (learnerFlag m) r y).2 a.2 : ℝ) * f a := by
  rw [protocolModel_action]
  cases r with
  | false => simpa [InterventionNumerics.rates, numerical_rates_eq] using action_lintegral m y f
  | true =>
      simp [restrainAction, Kernel.deterministic_apply, InterventionNumerics.rates,
        Fintype.sum_prod_type, sum_bool, boolMass]

theorem protocol_update_dirac (m : Mode) (r u : Bool) (y : Y) (a : Action) (x : Bool) :
    (protocolModel m r u).generator.update ((y, a), x) =
      Measure.dirac (InterventionNumerics.next (learnerFlag m) u y a) := by
  rw [protocolModel_update]
  cases u with
  | false =>
      change update m ((y,a),x) = Measure.dirac (OccupationNumerics.next (learnerFlag m) y a)
      rw [numerical_next_eq]
      exact update_dirac m ((y,a),x)
  | true => simp [resetUpdate, Kernel.deterministic_apply, InterventionNumerics.next]

/-- All eight exact rational entries are atoms of the corresponding original
typed induced kernels, with intervention application expanded through the
primitive action/world/update identities above. -/
theorem protocol_atom_eq (m : Mode) (r u : Bool) (y z : Y) :
    (protocolModel m r u).inducedKernel y {z} =
      ENNReal.ofReal (InterventionNumerics.entry (learnerFlag m) r u y z : ℝ) := by
  classical
  rw [StrategicWorldModel.inducedKernel_apply _ _ (measurableSet_singleton z)]
  simp only [protocolModel_world]
  change (∫⁻ a, ∫⁻ x, ((protocolModel m r u).generator.update ((y,a),x))
    {q | (q,x) ∈ ({z} : Set Y)} ∂coin (pRep y.2 a)
      ∂(protocolModel m r u).generator.action y) = _
  rw [protocol_action_lintegral]
  have hinter (a : Action) :
      (∫⁻ x, ((protocolModel m r u).generator.update ((y,a),x))
        {q | (q,x) ∈ ({z} : Set Y)} ∂coin (pRep y.2 a)) =
      ENNReal.ofReal (boolMass (pRep y.2 a) z.2 : ℝ) *
        if InterventionNumerics.next (learnerFlag m) u y a = z.1 then 1 else 0 := by
    simp_rw [protocol_update_dirac]
    rw [coin_lintegral]
    rcases z with ⟨qz, xz⟩
    cases xz <;> simp [Measure.dirac_apply, Set.indicator, boolMass, mul_ite, add_comm]
  simp_rw [hinter]
  simp_rw [ofReal_mass_term _ _ _
    (boolMass_nonneg _ (protocol_rates_bounds m r y).1 _)
    (boolMass_nonneg _ (protocol_rates_bounds m r y).2 _)
    (boolMass_nonneg _ (pRep_bounds y.2 _) _)]
  unfold InterventionNumerics.entry
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    push_cast <;> rfl
  · intro a _
    exact_mod_cast mul_nonneg
      (mul_nonneg (mul_nonneg
        (boolMass_nonneg _ (protocol_rates_bounds m r y).1 a.1)
        (boolMass_nonneg _ (protocol_rates_bounds m r y).2 a.2))
        (boolMass_nonneg _ (pRep_bounds y.2 a) z.2))
      (show (0 : ℚ) ≤ if InterventionNumerics.next (learnerFlag m) u y a = z.1 then 1 else 0 by
        split_ifs <;> norm_num)

theorem baseline_atom_eq (m : Mode) (y z : Y) :
    (model m).inducedKernel y {z} =
      ENNReal.ofReal (InterventionNumerics.entry (learnerFlag m) false false y z : ℝ) :=
  protocol_atom_eq m false false y z

theorem action_atom_eq (m : Mode) (y z : Y) :
    (Jaction m).intervention.apply.inducedKernel y {z} =
      ENNReal.ofReal (InterventionNumerics.entry (learnerFlag m) true false y z : ℝ) :=
  protocol_atom_eq m true false y z

theorem update_atom_eq (m : Mode) (y z : Y) :
    (Jupdate m).intervention.apply.inducedKernel y {z} =
      ENNReal.ofReal (InterventionNumerics.entry (learnerFlag m) false true y z : ℝ) :=
  protocol_atom_eq m false true y z

theorem joint_atom_eq (m : Mode) (y z : Y) :
    (Jjoint m).intervention.apply.inducedKernel y {z} =
      ENNReal.ofReal (InterventionNumerics.entry (learnerFlag m) true true y z : ℝ) :=
  protocol_atom_eq m true true y z

/-- All-horizon bridge for terminal repletion, with no intermediate killing. -/
theorem kernelTerminal_eq_rational (m : Mode) (r u : Bool) (n : ℕ) (y : Y) :
    kernelTerminal (protocolModel m r u).inducedKernel n y =
      ENNReal.ofReal (InterventionNumerics.terminal (learnerFlag m) r u n y : ℝ) := by
  induction n generalizing y with
  | zero => rcases y with ⟨q,x⟩; cases x <;>
      simp [kernelTerminal, InterventionNumerics.terminal, indicator]
  | succ n ih =>
      simp only [kernelTerminal, ih, protocol_atom_eq]
      have hmul (z : Y) :
          ENNReal.ofReal (InterventionNumerics.terminal (learnerFlag m) r u n z : ℝ) *
            ENNReal.ofReal (InterventionNumerics.entry (learnerFlag m) r u y z : ℝ) =
          ENNReal.ofReal ((InterventionNumerics.terminal (learnerFlag m) r u n z : ℝ) *
            (InterventionNumerics.entry (learnerFlag m) r u y z : ℝ)) := by
        rw [ENNReal.ofReal_mul (by exact_mod_cast
          (InterventionNumerics.terminal_bounds (learnerFlag m) r u n z).1)]
      simp_rw [hmul]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        simp only [InterventionNumerics.terminal]
        push_cast
        apply Finset.sum_congr rfl
        intro z _
        ring
      · intro z _
        exact mul_nonneg
          (by exact_mod_cast (InterventionNumerics.terminal_bounds (learnerFlag m) r u n z).1)
          (by exact_mod_cast InterventionNumerics.entry_nonneg (learnerFlag m) r u y z)

theorem original_property_eq_rational (m : Mode) (r u : Bool) (y : Y) :
    baselinePropertyValue property (protocolModel m r u) y =
      (InterventionNumerics.terminal (learnerFlag m) r u propertyHorizon y : ℝ) := by
  rw [baselineProperty_eq_kernelTerminal, kernelTerminal_eq_rational,
    ENNReal.toReal_ofReal]
  exact_mod_cast (InterventionNumerics.terminal_bounds (learnerFlag m) r u propertyHorizon y).1

end PermanssonResearch.X1
