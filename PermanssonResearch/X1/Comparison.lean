import PermanssonResearch.X1.MPECertificate
import PermanssonResearch.X1.TypedModels
import PermanssonResearch.ConstitutiveQuasi.ComparisonTransport
import PermanssonLean.Regime.GeneratedRegime

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace PermanssonResearch.X1

set_option autoImplicit false
open PermanssonLean

/-- The very policy in both-player Bellman certificates is the actual E
generator's joint law, not an unrelated rational policy with similar outcomes. -/
theorem equilibrium_action_implements_policy (y : Y) :
    (model .equilibrium).generator.action y =
      (coin (piExtract y.2)).prod (coin (piExtract y.2)) := rfl

noncomputable def restrainAction : Kernel Y Action :=
  Kernel.deterministic (fun _ => (false, false)) Measurable.of_discrete

instance restrainAction_isMarkov : IsMarkovKernel restrainAction := by
  unfold restrainAction; infer_instance

noncomputable def resetUpdate : Kernel UI Memory :=
  Kernel.deterministic (fun _ => (1, 1)) Measurable.of_discrete

instance resetUpdate_isMarkov : IsMarkovKernel resetUpdate := by
  unfold resetUpdate; infer_instance

noncomputable def restrainReset : StrategicGenerator Memory Bool Action :=
  ⟨restrainAction, resetUpdate, inferInstance, inferInstance⟩

inductive Component | action | update | joint
  deriving DecidableEq

def componentTarget : Component → InterventionTarget
  | .action => .actionSelection
  | .update => .strategicUpdate
  | .joint => .jointStrategic

noncomputable def family (m : Mode) : InterventionFamily (model m) Component where
  targetOf := componentTarget
  admissible
    | .action, r => r.kernel = restrainAction
    | .update, r => r.kernel = resetUpdate
    | .joint, r => r = restrainReset

noncomputable def Jaction (m : Mode) : AdmissibleStrategicIntervention (family m) where
  intervention := ⟨.action, ⟨restrainAction, inferInstance⟩⟩
  accepted := rfl
  strategic := InterventionTarget.isStrategic_actionSelection

noncomputable def Jupdate (m : Mode) : AdmissibleStrategicIntervention (family m) where
  intervention := ⟨.update, ⟨resetUpdate, inferInstance⟩⟩
  accepted := rfl
  strategic := InterventionTarget.isStrategic_strategicUpdate

noncomputable def Jjoint (m : Mode) : AdmissibleStrategicIntervention (family m) where
  intervention := ⟨.joint, restrainReset⟩
  accepted := rfl
  strategic := InterventionTarget.isStrategic_jointStrategic

theorem interventions_world_fixed (m : Mode)
    (J : AdmissibleStrategicIntervention (family m)) : J.intervention.apply.world = world :=
  J.world_eq

/-- The registered singleton comparison cannot satisfy the frozen ORIGINAL
path-law nontriviality gate. Randomness within one law does not supply two
distinct starts. Accordingly the rational receipt reports pointwise effects,
not an original constitutive-margin certificate. -/
theorem singleton_starts_not_pathLawNontrivial (m : Mode) :
    ¬ ∃ y₁ ∈ pointwiseStarts, ∃ y₂ ∈ pointwiseStarts,
      (model m).pathLaw (Measure.dirac y₁) ≠ (model m).pathLaw (Measure.dirac y₂) := by
  simp [pointwiseStarts]

/-- Prospective v2 takes the WHOLE registered region. Its distinct time-zero
states supply the original nontriviality gate, even for the equilibrium model
whose projected world policies ignore memory. This is not descriptor richness. -/
theorem region_pathLawNontrivial (m : Mode) :
    ∃ y₁ ∈ comparisonStarts, ∃ y₂ ∈ comparisonStarts,
      (model m).pathLaw (Measure.dirac y₁) ≠ (model m).pathLaw (Measure.dirac y₂) := by
  refine ⟨y0, rfl, ((0, 0), true), rfl, ?_⟩
  exact PermanssonResearch.ConstitutiveQuasi.pointStarted_pathLaw_ne_of_ne _ (by decide)

/-- Distinct stationary-law candidates, supported by exact rational invariant
equations in the executable receipt. No occupation convergence theorem is
asserted by recording these separate target data. -/
def targetReplete : Mode → ℚ
  | .equilibrium => 5 / 12
  | .learner => 44984685451641390245 / 355006278148174557117

theorem targetReplete_bounds (m : Mode) : 0 ≤ targetReplete m ∧ targetReplete m ≤ 1 := by
  cases m <;> norm_num [targetReplete]

theorem targetReplete_ne : targetReplete .equilibrium ≠ targetReplete .learner := by
  norm_num [targetReplete]

noncomputable def specification (m : Mode) : RegimeSpecification Y Bool where
  region := region
  region_measurable := MeasurableSet.of_discrete
  basin := basin
  basin_measurable := MeasurableSet.of_discrete
  basin_subset_region := fun _ h => h
  descriptor := descriptor
  descriptor_measurable := Measurable.of_discrete
  target := ⟨coin (targetReplete m), coin_probability _ (targetReplete_bounds m)⟩
  convergenceMode := ConvergenceMode.almostSureWeak Y Bool

/-- Actual original comparison-set object for prospective v2. The original
singleton could not inhabit this type. Canonical-property-to-calculated-margin
numerical transport remains an additional proof obligation. -/
noncomputable def comparisonSet (m : Mode) :
    RegimeSpecification.ConstitutiveComparisonSet (model m) (specification m) where
  states := comparisonStarts
  states_measurable := MeasurableSet.of_discrete
  states_subset_basin := fun _ h => h
  pathLawNontrivial := region_pathLawNontrivial m

/-- Both models lose 7/20 of replete-region mass at the registered start in
one actual typed transition. This is a killed-persistence stage, not a hit test. -/
theorem replete_one_step_leaks (m : Mode) :
    (model m).inducedKernel y0 region = (13 / 20 : ℝ≥0∞) := by
  rw [StrategicWorldModel.inducedKernel_apply _ _ MeasurableSet.of_discrete]
  change (∫⁻ a, ∫⁻ x, (update m ((y0, a), x)) {q | (q, x) ∈ region}
    ∂coin (pRep y0.2 a) ∂action m y0) = _
  rw [action_lintegral]
  cases m <;>
    norm_num [Fintype.sum_prod_type, sum_bool, coin_lintegral, update,
      Kernel.deterministic_apply, Measure.dirac_apply, region,
      extractionRate, piExtract, learnerExtract, y0, pRep, indicator, boolMass]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).1
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_mul]

/-- For either strategic generator, NO choice of occupation target or
convergence mode can turn the leaking replete region into an Exact GR. -/
theorem replete_not_exactGR (m : Mode) (spec : RegimeSpecification Y Bool)
    (hregion : spec.region = region) (reference : Measure Y) :
    ¬ RegimeSpecification.IsExactGeneratedRegime (model m) spec reference := by
  intro h
  have hinv := RegimeSpecification.exactGR_exactlyInvariant _ _ _ h
  have hstart : y0 ∈ spec.region := by rw [hregion]; rfl
  have hmass := hinv y0 hstart
  rw [hregion, replete_one_step_leaks] at hmass
  have hreal := congrArg ENNReal.toReal hmass
  norm_num at hreal

end PermanssonResearch.X1
