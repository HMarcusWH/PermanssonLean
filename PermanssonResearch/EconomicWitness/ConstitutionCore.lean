import PermanssonResearch.EconomicWitness.Geometry
import PermanssonLean.Regime.Persistence
import PermanssonLean.Intervention.Apply
import PermanssonLean.Regime.GroundedUniformPermansson

/-! Actual strategic intervention, original margin one, and grounded PR. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace PermanssonResearch.EconomicWitness
open PermanssonLean PermanssonLean.RegimeSpecification ActionTrace
set_option autoImplicit false

noncomputable def extractionAction : Kernel Y Action :=
  Kernel.deterministic (fun _ => (true,false)) Measurable.of_discrete

instance extractionAction_markov : IsMarkovKernel extractionAction := by
  unfold extractionAction
  infer_instance

noncomputable def family : InterventionFamily model Unit where
  targetOf _ := .actionSelection
  admissible _ r := r.kernel = extractionAction

noncomputable def extractionIntervention : AdmissibleStrategicIntervention family where
  intervention := ⟨(), ⟨extractionAction, inferInstance⟩⟩
  accepted := rfl
  strategic := InterventionTarget.isStrategic_actionSelection

theorem intervention_world_fixed : extractionIntervention.intervention.apply.world = model.world :=
  extractionIntervention.world_eq

theorem intervention_update_fixed : extractionIntervention.intervention.apply.generator.update = unitUpdate := rfl

noncomputable def treatedModel : StrategicWorldModel Unit World Action where
  generator := {
    action := extractionAction
    update := unitUpdate
    action_isMarkov := inferInstance
    update_isMarkov := by unfold unitUpdate; infer_instance }
  world := world
  world_isMarkov := inferInstance

theorem intervention_applied : extractionIntervention.intervention.apply = treatedModel := rfl

noncomputable def comparisonSet : ConstitutiveComparisonSet model specification where
  states := region
  states_measurable := MeasurableSet.of_discrete
  states_subset_basin := Set.Subset.rfl
  pathLawNontrivial := original_assumption41.2.2.2

/-- The declared complete-path property; its set is a measurable countable intersection. -/
noncomputable def survivalProperty : RegimePropertyMap Y ℝ :=
  fun law => (law.toMeasure (survivesForeverSet specification)).toReal

theorem baseline_value_one (y : Y) (hy : y ∈ region) :
    baselinePropertyValue survivalProperty model y = 1 := by
  change (model.pathLaw (Measure.dirac y) (survivesForeverSet specification)).toReal = 1
  rw [show model.pathLaw (Measure.dirac y) (survivesForeverSet specification) = 1 from
    exactInvariant_survivalForever model specification original_exact_invariance hy]
  norm_num

/-- The actual intervention only changes α, and sends the next world to collapse. -/
theorem intervened_region_mass_zero (y : Y) :
    extractionIntervention.intervention.apply.inducedKernel y region = 0 := by
  rw [intervention_applied]
  rw [StrategicWorldModel.inducedKernel_apply _ _ MeasurableSet.of_discrete]
  rcases y with ⟨u,x⟩
  cases u
  fin_cases x <;>
    norm_num [treatedModel, extractionAction, unitUpdate, world, worldRow, Row.measure, Row.pure,
      region, Fin.sum_univ_three, Kernel.deterministic_apply, Measure.dirac_apply,
      lintegral_add_measure, lintegral_smul_measure]

theorem intervened_value_zero (y : Y) (hy : y ∈ region) :
    intervenedPropertyValue survivalProperty extractionIntervention.intervention y = 0 := by
  have hfinite : survivalProbability extractionIntervention.intervention.apply specification y 1 = 0 := by
    rw [survivalProbability_eq_killedSurvivalMass _ specification 1 hy,
      killedSurvivalMass_one]
    exact intervened_region_mass_zero y
  have hforever : extractionIntervention.intervention.apply.pathLaw (Measure.dirac y)
      (survivesForeverSet specification) = 0 :=
    measure_mono_null (survivesForeverSet_subset_survivesThroughSet specification 1) hfinite
  change (extractionIntervention.intervention.apply.pathLaw (Measure.dirac y)
      (survivesForeverSet specification)).toReal = 0
  rw [hforever]
  norm_num

theorem effect_one (y : Y) (hy : y ∈ region) :
    constitutiveEffect model survivalProperty extractionIntervention y = 1 := by
  unfold constitutiveEffect
  rw [baseline_value_one y hy, intervened_value_zero y hy]
  norm_num

/-- The ORIGINAL uniform constitutive margin, on both functioning starts. -/
theorem original_constitutive_margin_one :
    constitutiveMargin model specification family survivalProperty comparisonSet extractionIntervention = 1 := by
  have hi : constitutiveEffect model survivalProperty extractionIntervention '' comparisonSet.states =
      ({1} : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact Set.mem_singleton_iff.mpr (effect_one y hy)
    · intro hr
      have heq : r = 1 := Set.mem_singleton_iff.mp hr
      subst r
      exact ⟨((),0), by simp [comparisonSet, region], effect_one ((),0) (by simp [region])⟩
  unfold constitutiveMargin
  rw [hi]
  simp

theorem original_uniform_constitution :
    IsUniformlyStrategicallyConstitutive model specification family survivalProperty comparisonSet extractionIntervention :=
  ⟨1, by norm_num, by rw [original_constitutive_margin_one]⟩

noncomputable def worldSurvivalProperty : RegimePropertyMap World ℝ :=
  fun law => (law.toMeasure {w : ℕ → World | ∀ t, w t ≠ 2}).toReal

theorem worldSurvival_measurable : MeasurableSet {w : ℕ → World | ∀ t, w t ≠ 2} := by
  have heq : {w : ℕ → World | ∀ t, w t ≠ 2} = ⋂ t : ℕ, {w | w t ≠ 2} := by ext w; simp
  rw [heq]
  apply MeasurableSet.iInter
  intro t
  exact (MeasurableSet.of_discrete : MeasurableSet {x : World | x ≠ 2}).preimage (measurable_pi_apply t)

/-- Global world relevance, including collapse, gives the exact original
protocol-relative property factorization. -/
noncomputable def survival_grounded_factor :
    GloballyFactorsThroughRelevanceMap specification survivalProperty grounding where
  groundedProperty := worldSurvivalProperty
  factor := by
    intro law
    change (law.toMeasure (survivesForeverSet specification)).toReal =
      ((law.toMeasure.map grounding.pathMap) {w : ℕ → World | ∀ t, w t ≠ 2}).toReal
    rw [Measure.map_apply grounding.pathMap_measurable worldSurvival_measurable]
    rfl

theorem original_grounded_property :
    IsGroundedPropertyRelative model specification family survivalProperty grounding extractionIntervention :=
  survival_grounded_factor.relative model specification family survivalProperty grounding extractionIntervention

end PermanssonResearch.EconomicWitness

