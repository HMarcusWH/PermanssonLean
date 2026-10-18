import PermanssonResearch.EconomicWitness.Model
import PermanssonLean.Regime.GeneratedRegime
import PermanssonLean.Regime.Relevance
import PermanssonLean.Regime.ExitTime
import Mathlib.MeasureTheory.Measure.Count

/-! Exact original geometric, invariant, relevance and nondegeneracy gates. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace PermanssonResearch.EconomicWitness
open PermanssonLean PermanssonLean.RegimeSpecification ActionTrace
set_option autoImplicit false

noncomputable def reference : Measure Y := Measure.count

theorem region_eq_pair : region = ({((),0),((),1)} : Set Y) := by
  ext y
  rcases y with ⟨u,x⟩
  cases u
  fin_cases x <;> simp [region]

theorem original_assumption41 : Assumption41 model specification reference := by
  refine ⟨⟨((),0), by simp [specification, region]⟩, ?_, ?_, ?_⟩
  · right
    have hs : 0 < reference ({((),(0:World))} : Set Y) := by simp [reference]
    exact hs.trans_le (measure_mono (Set.singleton_subset_iff.mpr (by simp [specification, region])))
  · exact ⟨((),0), by simp [specification, region], ((),1),
      by simp [specification, region], by decide⟩
  · apply two_states_implies_basinPathLawNontrivial
    exact ⟨((),0), by simp [specification, region], ((),1),
      by simp [specification, region], by decide⟩

/-- Every actual baseline kernel atom, in the frozen action→world→unit-update order. -/
theorem induced_atom (y z : Y) :
    model.inducedKernel y {z} =
      if y.2 = 2 then (if z.2 = 2 then 1 else 0)
      else if z.2 = 2 then 0 else (1/2 : ℝ≥0∞) := by
  rw [StrategicWorldModel.inducedKernel_apply model y (measurableSet_singleton z)]
  rcases y with ⟨u,x⟩
  rcases z with ⟨v,z⟩
  cases u
  cases v
  fin_cases x <;> fin_cases z <;>
    norm_num [model, baselineAction, unitUpdate, world, worldRow, fairRow, Row.measure,
      Row.pure, Fin.sum_univ_three, Kernel.deterministic_apply, Measure.dirac_apply,
      lintegral_add_measure, lintegral_smul_measure]
  all_goals
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num

theorem original_exact_invariance : IsExactlyInvariant model specification := by
  intro y hy
  have hx : y.2 ≠ 2 := hy
  change model.inducedKernel y region = 1
  rw [region_eq_pair]
  have hfin : ({((),(0:World)),((),(1:World))} : Set Y) =
      (↑({((),(0:World)),((),(1:World))} : Finset Y) : Set Y) := by simp
  rw [hfin, ← sum_measure_singleton]
  norm_num [induced_atom, hx]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]

theorem descriptorLaw_zero (y : Y) :
    descriptorLaw model specification (diracProba y) 0 = diracProba y.2 := by
  apply ProbabilityMeasure.toMeasure_injective
  change (model.pathLaw (Measure.dirac y)).map (fun w => (w 0).2) = Measure.dirac y.2
  change (model.pathLaw (Measure.dirac y)).map (Prod.snd ∘ (fun w : ℕ → Y => w 0)) = _
  rw [← Measure.map_map measurable_snd (measurable_pi_apply 0), StrategicWorldModel.pathLaw_eval_zero]
  simp

theorem original_descriptor_nondegenerate : IsDescriptorNondegenerate model specification := by
  refine ⟨((),0), by simp [specification, region], 0,
    ((),1), by simp [specification, region], 0, ?_⟩
  rw [descriptorLaw_zero, descriptorLaw_zero]
  intro hh
  have hn : (0 : World) = 1 := injective_diracProba hh
  exact (by decide : (0 : World) ≠ 1) hn

/-- Identity world relevance is defined everywhere, including collapse. -/
noncomputable def grounding : GroundedRelevanceMap specification World where
  observe := Prod.snd
  observe_measurable := measurable_snd
  regimeRegion := {x | x ≠ 2}
  regimeRegion_measurable := MeasurableSet.of_discrete
  region_preimage := rfl
  descriptor := id
  descriptor_measurable := measurable_id
  descriptor_factor := rfl

/-- The target has genuine positive mass on both functioning observations. -/
theorem target_two_positive_atoms : 0 < target.toMeasure {0} ∧ 0 < target.toMeasure {1} := by
  change 0 < fairRow.measure {0} ∧ 0 < fairRow.measure {1}
  rw [Row.measure_singleton, Row.measure_singleton]
  norm_num [fairRow]

end PermanssonResearch.EconomicWitness
