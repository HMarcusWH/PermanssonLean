import PermanssonResearch.GrammarRobust.BooleanDynamics
import PermanssonLean.Regime.Persistence
import Mathlib.Tactic

/-!
# Lane B — real persistent-regime constitution and quantitative witness

The defining property is the probability of remaining in the *frozen*
nontrivial regime region at every time t ≥ 0, an infinite-path event.
The baseline and either singleton perturbation persist almost surely;
joint replacement exits after one step with probability one.
All assertions are about the canonical α → P → U path law.
-/

open MeasureTheory ProbabilityTheory Set
namespace PermanssonResearch
namespace GrammarRobust
namespace BooleanPersistence

open PermanssonLean PermanssonLean.RegimeSpecification
open BooleanModel BooleanBaseline BooleanDynamics

noncomputable def actionBlock : AllowedBlock fine :=
  ⟨actionOnly, trivial⟩
noncomputable def updateBlock : AllowedBlock fine :=
  ⟨updateOnly, trivial⟩
noncomputable def jointBlock : AllowedBlock fine :=
  ⟨joint, trivial⟩

/-- A direct application of the frozen world transition P and the updated
actual α/U kernels: every action-only path remains in B after each step. -/
theorem actionExactlyInvariant :
    IsExactlyInvariant (blockModel baseline bank fine actionOnly) spec := by
  intro y hy
  rw [actionOnly_inducedKernel]
  rw [Measure.dirac_apply_of_mem]
  exact (show actionDest ∈ region by
    simp [region, actionDest, forbidden])

theorem updateExactlyInvariant :
    IsExactlyInvariant (blockModel baseline bank fine updateOnly) spec := by
  intro y hy
  rw [updateOnly_inducedKernel]
  rw [Measure.dirac_apply_of_mem]
  exact (show updateDest ∈ region by
    simp [region, updateDest, forbidden])

theorem actionSurvivesForever {y : Y} (hy : y ∈ region) :
    survivalForeverProbability
      (blockModel baseline bank fine actionOnly) spec y = 1 :=
  exactInvariant_survivalForever _ spec actionExactlyInvariant
    (by simpa [spec] using hy)

theorem updateSurvivesForever {y : Y} (hy : y ∈ region) :
    survivalForeverProbability
      (blockModel baseline bank fine updateOnly) spec y = 1 :=
  exactInvariant_survivalForever _ spec updateExactlyInvariant
    (by simpa [spec] using hy)

theorem jointSurvivalOne_eq_zero {y : Y} (hy : y ∈ region) :
    survivalProbability (blockModel baseline bank fine joint) spec y 1 = 0 := by
  rw [survivalProbability_eq_killedSurvivalMass _ spec 1
      (by simpa [spec] using hy), killedSurvivalMass_one]
  rw [joint_inducedKernel]
  rw [Measure.dirac_apply' jointDest spec.region_measurable]
  simp [spec, region, jointDest, forbidden]

theorem jointSurvivesForever_eq_zero {y : Y} (hy : y ∈ region) :
    survivalForeverProbability (blockModel baseline bank fine joint) spec y = 0 := by
  apply le_antisymm ?_ bot_le
  calc
    survivalForeverProbability (blockModel baseline bank fine joint) spec y ≤
        survivalProbability (blockModel baseline bank fine joint) spec y 1 :=
          measure_mono (survivesForeverSet_subset_survivesThroughSet spec 1)
    _ = 0 := jointSurvivalOne_eq_zero hy

/-- A fixed real-valued full-path probability; unlike a time-one statistic,
it is a literal regime persistence observable. -/
noncomputable def persistenceProperty : RegimePropertyMap Y ℝ :=
  fun μ => (μ.toMeasure (survivesForeverSet spec)).toReal

theorem baselineProperty_one {y : Y} (hy : y ∈ region) :
    baselinePropertyValue persistenceProperty baseline y = 1 := by
  change (survivalForeverProbability baseline spec y).toReal = 1
  rw [exactInvariant_survivalForever baseline spec
    exactlyInvariant (by simpa [spec] using hy)]
  simp

theorem actionProperty_one {y : Y} (hy : y ∈ region) :
    intervenedPropertyValue persistenceProperty
      (admittedBlockIntervention baseline bank fine actionBlock).intervention y = 1 := by
  change (survivalForeverProbability
    (admittedBlockIntervention baseline bank fine actionBlock).intervention.apply
    spec y).toReal = 1
  rw [admittedBlockIntervention_apply]
  change (survivalForeverProbability
    (blockModel baseline bank fine actionOnly) spec y).toReal = 1
  rw [actionSurvivesForever hy]
  simp

theorem updateProperty_one {y : Y} (hy : y ∈ region) :
    intervenedPropertyValue persistenceProperty
      (admittedBlockIntervention baseline bank fine updateBlock).intervention y = 1 := by
  change (survivalForeverProbability
    (admittedBlockIntervention baseline bank fine updateBlock).intervention.apply
    spec y).toReal = 1
  rw [admittedBlockIntervention_apply]
  change (survivalForeverProbability
    (blockModel baseline bank fine updateOnly) spec y).toReal = 1
  rw [updateSurvivesForever hy]
  simp

theorem jointProperty_zero {y : Y} (hy : y ∈ region) :
    intervenedPropertyValue persistenceProperty
      (admittedBlockIntervention baseline bank fine jointBlock).intervention y = 0 := by
  change (survivalForeverProbability
    (admittedBlockIntervention baseline bank fine jointBlock).intervention.apply
    spec y).toReal = 0
  rw [admittedBlockIntervention_apply]
  change (survivalForeverProbability
    (blockModel baseline bank fine joint) spec y).toReal = 0
  rw [jointSurvivesForever_eq_zero hy]
  simp

theorem jointEffect_eq_one {y : Y} (hy : y ∈ comparison.states) :
    blockEffect baseline bank fine jointBlock persistenceProperty y = 1 := by
  have hregion : y ∈ region := by
    exact (show y ∈ spec.region from
      comparison.states_subset_region baseline spec hy)
  unfold blockEffect constitutiveEffect
  rw [baselineProperty_one hregion, jointProperty_zero hregion]
  norm_num

theorem actionEffect_eq_zero {y : Y} (hy : y ∈ comparison.states) :
    blockEffect baseline bank fine actionBlock persistenceProperty y = 0 := by
  have hregion : y ∈ region :=
    comparison.states_subset_region baseline spec hy
  unfold blockEffect constitutiveEffect
  rw [baselineProperty_one hregion, actionProperty_one hregion]
  simp

theorem updateEffect_eq_zero {y : Y} (hy : y ∈ comparison.states) :
    blockEffect baseline bank fine updateBlock persistenceProperty y = 0 := by
  have hregion : y ∈ region :=
    comparison.states_subset_region baseline spec hy
  unfold blockEffect constitutiveEffect
  rw [baselineProperty_one hregion, updateProperty_one hregion]
  simp

theorem jointMargin_eq_one :
    blockMargin baseline bank fine jointBlock spec persistenceProperty comparison = 1 := by
  unfold blockMargin constitutiveMargin
  have hnonempty : (constitutiveEffect baseline persistenceProperty
      (admittedBlockIntervention baseline bank fine jointBlock) ''
      comparison.states).Nonempty := by
    obtain ⟨y,hy⟩ := comparison.states_nonempty baseline spec
    exact ⟨_, ⟨y, hy, rfl⟩⟩
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, by rintro x ⟨y,hy,rfl⟩; exact dist_nonneg⟩
    · obtain ⟨y,hy⟩ := comparison.states_nonempty baseline spec
      exact ⟨y,hy,jointEffect_eq_one hy⟩
  · apply le_csInf hnonempty
    rintro x ⟨y,hy,rfl⟩
    change 1 ≤ blockEffect baseline bank fine jointBlock persistenceProperty y
    rw [jointEffect_eq_one hy]

theorem uniformRelativePR :
    IsUniformGeneralizedPermanssonRegimeRelative
      baseline spec referenceMeasure
      (blockFamily baseline bank fine) persistenceProperty comparison
      (admittedBlockIntervention baseline bank fine jointBlock) := by
  refine ⟨exactGR, ?_⟩
  apply (uniformlyConstitutive_iff_margin_pos
    baseline spec (blockFamily baseline bank fine) persistenceProperty
    comparison (admittedBlockIntervention baseline bank fine jointBlock)).2
  change 0 < blockMargin baseline bank fine jointBlock
    spec persistenceProperty comparison
  rw [jointMargin_eq_one]
  norm_num

theorem genuineRelativePR :
    IsGeneralizedPermanssonRegimeRelative
      baseline spec referenceMeasure
      (blockFamily baseline bank fine) persistenceProperty comparison
      (admittedBlockIntervention baseline bank fine jointBlock) :=
  uniformRelativePR_implies_relativePR
    baseline spec referenceMeasure (blockFamily baseline bank fine)
    persistenceProperty comparison
    (admittedBlockIntervention baseline bank fine jointBlock) uniformRelativePR

end BooleanPersistence
end GrammarRobust
end PermanssonResearch
