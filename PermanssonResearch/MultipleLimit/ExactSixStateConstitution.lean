import PermanssonResearch.MultipleLimit.TypedEventResponse
import PermanssonLean.Regime.UniformPermansson
import Mathlib.Tactic

/-!
# C6 — original unweakened uniform relative Permansson constitution

The old Exact GR status comes from C2/C3, not from redefining a GR.
The one frozen descriptor-event property is evaluated on the actual
baseline and typed intervened infinite path laws. Every state of the
original nontrivial comparison set changes from probability 1 to 0.
The canonical P and U primitives are unchanged.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateConstitution

open PermanssonLean
open PermanssonLean.RegimeSpecification
open ReverseSolver.FiniteStrategicRealization
open ExactSixStateTyped
open ExactSixStateObservedGR
open ExactSixStateTargetDisruption
open TypedEventResponse

noncomputable section

abbrev SixY := JointState Unit (Fin 6)

/-- B1 is exactly the ORIGINAL ex-ante two-point basin, with a
genuine baseline infinite-path nontriviality certificate. -/
def comparison : ConstitutiveComparisonSet typedModel observedSpec where
  states := observedBasin
  states_measurable := (Set.toFinite observedBasin).measurableSet
  states_subset_basin := Set.Subset.rfl
  pathLawNontrivial := observedAssumption41.2.2.2

/-- The compared states are precisely u and a0, both already in the
frozen original basin. No later choice after seeing the response. -/
theorem comparison_states (y : SixY) :
    y ∈ comparison.states ↔ y = decode (1 : Fin 6) ∨
      y = decode (2 : Fin 6) := by
  change y ∈ observedBasin ↔ _
  simp [observedBasin]

/-- The original quantitative effect is exactly 1 at BOTH declared
comparison starts, not merely positive on one convenient trajectory. -/
theorem effect_eq_one (y : SixY) (hy : y ∈ comparison.states) :
    constitutiveEffect typedModel fixedProperty intervention y = 1 := by
  obtain hyu | hya := (comparison_states y).mp hy
  · subst y
    unfold constitutiveEffect
    rw [baselineProperty_one,
      intervenedProperty_zero (1 : Fin 6) (Or.inl rfl)]
    norm_num
  · subst y
    unfold constitutiveEffect
    rw [baselineProperty_one,
      intervenedProperty_zero (2 : Fin 6) (Or.inr rfl)]
    norm_num

/-- Nonvacuous exact uniform margin: inf_{y in B1} |1-0| = 1. -/
theorem constitutiveMargin_eq_one :
    constitutiveMargin typedModel observedSpec
      (researchActionFamily sixStateMatrix) fixedProperty
      comparison intervention = 1 := by
  unfold constitutiveMargin
  have hnonempty :
      (constitutiveEffect typedModel fixedProperty intervention ''
          comparison.states).Nonempty := by
    obtain ⟨y,hy⟩ :=
      comparison.states_nonempty typedModel observedSpec
    exact ⟨_, ⟨y,hy,rfl⟩⟩
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, by rintro z ⟨y,hy,rfl⟩; exact dist_nonneg⟩
    · obtain ⟨y,hy⟩ :=
        comparison.states_nonempty typedModel observedSpec
      exact ⟨y,hy,effect_eq_one y hy⟩
  · apply le_csInf hnonempty
    rintro z ⟨y,hy,rfl⟩
    change 1 ≤ constitutiveEffect typedModel
      fixedProperty intervention y
    rw [effect_eq_one y hy]

/-- Original UNWEAKENED uniform relative Permansson classification.
The exact baseline GR and separate intervention-effect gates are both
proved; neither is assumed in the statement. -/
theorem uniformRelativePR :
    IsUniformGeneralizedPermanssonRegimeRelative
      typedModel observedSpec observedReference
      (researchActionFamily sixStateMatrix)
      fixedProperty comparison intervention := by
  refine ⟨observedExactGeneratedRegime, ?_⟩
  apply (uniformlyConstitutive_iff_margin_pos
    typedModel observedSpec
    (researchActionFamily sixStateMatrix)
    fixedProperty comparison intervention).2
  rw [constitutiveMargin_eq_one]
  norm_num

/-- Pointwise strategic constitution follows for the SAME frozen
protocol; no custom PR predicate or assumption substitution is used. -/
theorem genuineRelativePR :
    IsGeneralizedPermanssonRegimeRelative
      typedModel observedSpec observedReference
      (researchActionFamily sixStateMatrix)
      fixedProperty comparison intervention :=
  uniformRelativePR_implies_relativePR
    typedModel observedSpec observedReference
    (researchActionFamily sixStateMatrix)
    fixedProperty comparison intervention uniformRelativePR

/-- Family-level witness is provided by the exact typed strategic
intervention admitted under the predeclared constructed research family. -/
theorem genuineFamilyPR :
    IsGeneralizedPermanssonRegime
      typedModel observedSpec observedReference
      (researchActionFamily sixStateMatrix)
      fixedProperty comparison :=
  relativePR_implies_generalizedPR
    typedModel observedSpec observedReference
    (researchActionFamily sixStateMatrix)
    fixedProperty comparison intervention genuineRelativePR

theorem world_fixed :
    intervention.intervention.apply.world = typedModel.world :=
  actual_world_fixed

theorem update_fixed :
    intervention.intervention.apply.generator.update =
      typedModel.generator.update :=
  actual_update_fixed

end
end ExactSixStateConstitution
end MultipleLimit
end PermanssonResearch
