import PermanssonResearch.StrategicWorld.ActionTraceOriginalBridge
import PermanssonResearch.X1.FullStrategyCertificate
import PermanssonResearch.X1.OccupationNumerics

/-! Original X1 equilibrium path law is the exact state marginal of the trace law. -/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.X1
open ActionTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem strategy_bind_mass {α β : Type} [Fintype α] [Fintype β]
    (p : Row α) (q : α → Row β) (b : β) :
    (p.bind q).mass b = ∑ a, p.mass a * (q a).mass b := rfl

theorem strategy_map_mass {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (p : Row α) (f : α → β) (b : β) :
    (p.map f).mass b = ∑ a, if f a = b then p.mass a else 0 := by
  classical
  simp only [Row.map]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : f a = b <;> simp [h]

noncomputable def candidateOwnRow (y : Y) : Row Bool :=
  booleanRow (piExtract y.2) (piExtract_bounds _)

theorem strategy_boolMass_nonneg (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (b : Bool) :
    0 ≤ boolMass p b := by
  cases b <;> simp [boolMass, hp.1, sub_nonneg.mpr hp.2]

theorem strategy_world_atom_sum (p : ℚ) (q : Memory) (z : Y) :
    (∑ x : Bool, ENNReal.ofReal (boolMass p x : ℝ) *
      if (q,x) = z then 1 else 0) =
    ENNReal.ofReal (boolMass p z.2 : ℝ) * if q = z.1 then 1 else 0 := by
  rcases z with ⟨qz,xz⟩
  cases xz <;> simp [sum_bool, Prod.mk.injEq]

theorem strategy_ofReal_mass_term (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (P : Prop) [Decidable P] :
    ENNReal.ofReal (a : ℝ) * ENNReal.ofReal (b : ℝ) *
        (ENNReal.ofReal (c : ℝ) * if P then 1 else 0) =
      ENNReal.ofReal ((a*b*c*if P then 1 else 0 : ℚ) : ℝ) := by
  by_cases hP : P
  · simp only [hP,if_true,mul_one]
    push_cast
    rw [ENNReal.ofReal_mul (show 0 ≤ (a : ℝ)*(b : ℝ) from
      mul_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb)),
      ENNReal.ofReal_mul (by exact_mod_cast ha)]
  · simp [hP]

/-- The exact atom calculation uses only the original primitive-derived matrix
entry. It does not depend on stationary or occupation-limit conclusions. -/
theorem strategy_actual_kernel_atom (y z : Y) :
    (model .equilibrium).inducedKernel y {z} =
      ENNReal.ofReal (OccupationNumerics.entry false y z : ℝ) := by
  rw [inducedKernel_atom_entry]
  unfold transitionEntry
  simp_rw [strategy_world_atom_sum]
  simp_rw [strategy_ofReal_mass_term _ _ _
    (strategy_boolMass_nonneg _ (extractionRate_bounds .equilibrium y).1 _)
    (strategy_boolMass_nonneg _ (extractionRate_bounds .equilibrium y).2 _)
    (strategy_boolMass_nonneg _ (pRep_bounds y.2 _) _)]
  unfold OccupationNumerics.entry
  simp only [OccupationNumerics.rates,OccupationNumerics.next,extractionRate,nextMemory,
    Bool.false_eq_true,ite_false]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    push_cast <;> rfl
  · intro a ha
    exact_mod_cast mul_nonneg
      (mul_nonneg (mul_nonneg
        (strategy_boolMass_nonneg _ (piExtract_bounds _) _)
        (strategy_boolMass_nonneg _ (piExtract_bounds _) _))
        (strategy_boolMass_nonneg _ (pRep_bounds _ _) _))
      (show (0 : ℚ) ≤ if y.1 = z.1 then 1 else 0 by split_ifs <;> norm_num)

/-- The row identification required by the generic original-law bridge is
proved against the actual original α→P→U kernel, for both indexed players. -/
theorem equilibrium_stateStep_actual (i : Player) (y : Y) :
    (stateStep (strategyGame .equilibrium i) candidateOwnRow y).measure =
      (model .equilibrium).inducedKernel y := by
  classical
  apply Measure.ext_of_singleton
  intro z
  rw [Row.measure_singleton, strategy_actual_kernel_atom]
  congr 1
  rcases y with ⟨s,x⟩
  rcases z with ⟨t,z⟩
  fin_cases i <;> cases x <;> cases z <;> by_cases h : s = t
  all_goals
    norm_num [stateStep, candidateOwnRow, strategyGame, strategy_bind_mass, strategy_map_mass, booleanRow,
      OccupationNumerics.entry, OccupationNumerics.rates, OccupationNumerics.next,
      Fintype.sum_prod_type, sum_bool, extractionRate, nextMemory,
      piExtract, boolMass, deviationAction, pRep, indicator, h]

/-- Literal equality of probability measures on all original state-path events.
Reward remains evaluated on the richer action trace, before this erasure. -/
theorem baseline_trace_stateLaw_eq_original (i : Player) (μ : Row Y) :
    (canonicalLaw (strategyGame .equilibrium i) baselineBehavior μ).map statePath =
      (model .equilibrium).pathLaw μ.measure := by
  exact canonical_state_erasure_eq_original (model .equilibrium)
    (strategyGame .equilibrium i) candidateOwnRow μ (equilibrium_stateStep_actual i)

end PermanssonResearch.X1
