import PermanssonResearch.EconomicWitness.Constitution
import PermanssonResearch.EconomicWitness.Incentives

/-! Semantic negative tests for the economic witness's original gates. -/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.EconomicWitness.Regression
open PermanssonLean PermanssonLean.RegimeSpecification ActionTrace
set_option autoImplicit false

theorem world_replacement_not_strategic : ¬ InterventionTarget.worldTransition.IsStrategic := by
  simp [InterventionTarget.IsStrategic]

theorem singleton_comparison_rejected :
    ¬ (∃ y ∈ ({((),(0:World))} : Set Y), ∃ z ∈ ({((),(0:World))} : Set Y),
      model.pathLaw (Measure.dirac y) ≠ model.pathLaw (Measure.dirac z)) := by simp

noncomputable def constantDescriptorSpec : RegimeSpecification Y World :=
  { specification with descriptor := fun _ => 0, descriptor_measurable := measurable_const }

theorem constant_descriptor_rejected : ¬ DescriptorHasTwoValues constantDescriptorSpec := by
  simp [DescriptorHasTwoValues, constantDescriptorSpec]

def badObserve (y : Y) : World := if y.2 = 2 then 0 else y.2

/-- Fitting relevance only on the functioning region does not satisfy the
original global descriptor factorization: collapse must still be observed. -/
theorem absent_off_region_relevance_rejected :
    ¬ (specification.descriptor = id ∘ badObserve) := by
  intro hh
  have hc := congrFun hh ((),(2:World))
  norm_num [specification, badObserve] at hc

/-- The exact positive certificate includes both comparison starts. -/
theorem both_comparison_effects :
    constitutiveEffect model survivalProperty extractionIntervention ((),0) = 1 ∧
      constitutiveEffect model survivalProperty extractionIntervention ((),1) = 1 :=
  ⟨effect_one _ (by simp [region]), effect_one _ (by simp [region])⟩

/-- The deliberately altered extraction reward violates the actual Bellman
candidate at every functioning start, without invoking a malformed input. -/
theorem profitable_extraction_rejected : ¬ ((5 : ℝ) + (3/4 : ℝ) * 0 ≤ 4) := by norm_num

noncomputable def leakyRow : Row World where
  mass x := if x = 1 then 0 else 1/2
  nonneg _ := by split_ifs <;> norm_num
  total := by norm_num [Fin.sum_univ_three]

noncomputable def leakyWorld : Kernel (WorldInput Unit World Action) World :=
  Kernel.const _ leakyRow.measure

instance leakyWorld_markov : IsMarkovKernel leakyWorld := by
  unfold leakyWorld
  infer_instance

noncomputable def leakyModel : StrategicWorldModel Unit World Action :=
  { model with world := leakyWorld, world_isMarkov := inferInstance }

/-- A baseline world leak fails the ORIGINAL invariant-region gate. -/
theorem baseline_leak_rejected : ¬ IsExactlyInvariant leakyModel specification := by
  intro hh
  have hm := hh ((),(0:World)) (by simp [specification, region])
  rw [StrategicWorldModel.inducedKernel_apply _ _ MeasurableSet.of_discrete] at hm
  norm_num [leakyModel, model, baselineAction, unitUpdate, leakyWorld, leakyRow,
    Kernel.const_apply, Row.measure, Fin.sum_univ_three, Kernel.deterministic_apply,
    Measure.dirac_apply, specification, region, lintegral_add_measure, lintegral_smul_measure] at hm

theorem baseline_leak_not_original_exactGR : ¬ IsExactGeneratedRegime leakyModel specification reference := by
  intro hh
  exact baseline_leak_rejected (exactGR_exactlyInvariant _ _ _ hh)

end PermanssonResearch.EconomicWitness.Regression
