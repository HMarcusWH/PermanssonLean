import PermanssonResearch.RegimeExit.SwitchRouting
import PermanssonResearch.ReverseSolver.FiniteStrategicRealization
import Mathlib.Tactic

/-!
# C-Exit B — five-state rational strategic intervention fixtures

These are real action-selection/world-transition/strategic-update
factorizations. The shared P and U are literal object equalities.
The exact GR, almost-sure switching and occupation certificates are
separate proof targets; rows or Python results are not those certificates.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace PermanssonResearch.RegimeExit.SwitchWitnessModels

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization

set_option autoImplicit false

/-- Baseline 0 -> 1 -> 4, with 4 absorbing; destination 2 -> 3
and 3 absorbing. Baseline source B={0,1,4} is invariant. -/
def baselineMatrix : RationalMarkovMatrix 5 where
  entry := fun y z =>
    if y = 0 then
      if z = 1 then 1 else 0
    else if y = 1 then
      if z = 4 then 1 else 0
    else if y = 2 then
      if z = 3 then 1 else 0
    else if z = y then 1 else 0
  entry_nonneg := by
    intro y z
    split_ifs <;> norm_num
  row_sum_one := by
    intro y
    fin_cases y <;> norm_num [Fin.sum_univ_five]

/-- From 0 or 1, geometric exit to the target with hazard 1/2.
Every other row agrees exactly with the baseline. -/
def fullMatrix : RationalMarkovMatrix 5 where
  entry := fun y z =>
    if y = 0 then
      if z = 0 then 1/2 else if z = 2 then 1/2 else 0
    else if y = 1 then
      if z = 1 then 1/2 else if z = 3 then 1/2 else 0
    else if y = 2 then
      if z = 3 then 1 else 0
    else if z = y then 1 else 0
  entry_nonneg := by
    intro y z
    split_ifs <;> norm_num
  row_sum_one := by
    intro y
    fin_cases y <;> norm_num [Fin.sum_univ_five]

/-- Direct one-step 1/2 switch, with the other half absorbed at source 4.
This supplies the desired partial-routing negative/positive control. -/
def partialMatrix : RationalMarkovMatrix 5 where
  entry := fun y z =>
    if y = 0 then
      if z = 4 then 1/2 else if z = 2 then 1/2 else 0
    else if y = 1 then
      if z = 4 then 1/2 else if z = 3 then 1/2 else 0
    else if y = 2 then
      if z = 3 then 1 else 0
    else if z = y then 1 else 0
  entry_nonneg := by
    intro y z
    split_ifs <;> norm_num
  row_sum_one := by
    intro y
    fin_cases y <;> norm_num [Fin.sum_univ_five]

abbrev Y := JointState Unit (Fin 5)

noncomputable def baselineModel : StrategicWorldModel Unit (Fin 5) (Fin 5) :=
  realizedModel baselineMatrix

noncomputable def fullModel : StrategicWorldModel Unit (Fin 5) (Fin 5) :=
  realizedModel fullMatrix

noncomputable def partialModel : StrategicWorldModel Unit (Fin 5) (Fin 5) :=
  realizedModel partialMatrix

noncomputable def fullIntervention :
    AdmissibleStrategicIntervention (researchActionFamily baselineMatrix) :=
  rationalStrategicIntervention baselineMatrix fullMatrix

noncomputable def partialIntervention :
    AdmissibleStrategicIntervention (researchActionFamily baselineMatrix) :=
  rationalStrategicIntervention baselineMatrix partialMatrix

noncomputable def sourceSpec : RegimeSpecification Y (Fin 5) where
  region := {y | y.2 = 0 ∨ y.2 = 1 ∨ y.2 = 4}
  region_measurable := MeasurableSet.of_discrete
  basin := {y | y.2 = 0 ∨ y.2 = 1}
  basin_measurable := MeasurableSet.of_discrete
  basin_subset_region := by
    intro y hy
    rcases hy with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
  descriptor := Prod.snd
  descriptor_measurable := measurable_snd
  target := ⟨Measure.dirac (4 : Fin 5), inferInstance⟩
  convergenceMode := ConvergenceMode.almostSureWeak Y (Fin 5)

noncomputable def targetSpec : RegimeSpecification Y (Fin 5) where
  region := {y | y.2 = 2 ∨ y.2 = 3}
  region_measurable := MeasurableSet.of_discrete
  basin := {y | y.2 = 2 ∨ y.2 = 3}
  basin_measurable := MeasurableSet.of_discrete
  basin_subset_region := Set.Subset.rfl
  descriptor := Prod.snd
  descriptor_measurable := measurable_snd
  target := ⟨Measure.dirac (3 : Fin 5), inferInstance⟩
  convergenceMode := ConvergenceMode.almostSureWeak Y (Fin 5)

/-- The two regions do not merely have different labels; their physical
world-state subsets are disjoint. -/
theorem source_target_disjoint :
    Disjoint sourceSpec.region targetSpec.region := by
  apply Set.disjoint_left.mpr
  intro y hs ht
  rcases y with ⟨u,x⟩
  cases u
  change x = 0 ∨ x = 1 ∨ x = 4 at hs
  change x = 2 ∨ x = 3 at ht
  fin_cases x <;> simp_all

theorem actual_full_intervened_model :
    fullIntervention.intervention.apply = fullModel := by
  exact rationalStrategicIntervention_applied baselineMatrix fullMatrix

theorem actual_partial_intervened_model :
    partialIntervention.intervention.apply = partialModel := by
  exact rationalStrategicIntervention_applied baselineMatrix partialMatrix

/-- No change of the world or update kernels, only action selection. -/
theorem full_world_fixed :
    fullIntervention.intervention.apply.world = baselineModel.world := by
  exact rationalStrategicIntervention_world_fixed baselineMatrix fullMatrix

theorem partial_world_fixed :
    partialIntervention.intervention.apply.world = baselineModel.world := by
  exact rationalStrategicIntervention_world_fixed baselineMatrix partialMatrix

theorem full_update_fixed :
    fullIntervention.intervention.apply.generator.update =
      baselineModel.generator.update := by
  exact rationalStrategicIntervention_update_fixed baselineMatrix fullMatrix

/-- A direct kernel-level check of the genuinely induced 1/2 first-step
destination hazard, not yet the infinite-horizon routing proof. -/
theorem full_zero_to_two_half :
    fullModel.inducedKernel (decode (0 : Fin 5))
      (encode ⁻¹' ({2} : Set (Fin 5))) = (1/2 : ℝ≥0∞) := by
  change (realizedModel fullMatrix).inducedKernel (decode 0)
    (encode ⁻¹' ({2} : Set (Fin 5))) = _
  rw [inducedKernel_encodedEntry fullMatrix 0 2]
  norm_num [fullMatrix]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem partial_zero_to_two_half :
    partialModel.inducedKernel (decode (0 : Fin 5))
      (encode ⁻¹' ({2} : Set (Fin 5))) = (1/2 : ℝ≥0∞) := by
  change (realizedModel partialMatrix).inducedKernel (decode 0)
    (encode ⁻¹' ({2} : Set (Fin 5))) = _
  rw [inducedKernel_encodedEntry partialMatrix 0 2]
  norm_num [partialMatrix]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

end PermanssonResearch.RegimeExit.SwitchWitnessModels
