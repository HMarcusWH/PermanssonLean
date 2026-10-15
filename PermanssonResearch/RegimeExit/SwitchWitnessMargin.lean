import PermanssonResearch.RegimeExit.SwitchWitnessCertificate
import PermanssonResearch.RegimeExit.SwitchConstitution
import PermanssonResearch.RegimeExit.ExitAdversaries
import Mathlib.Tactic

/-!
# C-Exit B — nonvacuous positive 5-state strategic constitution

No geometric infinite-sum formula is needed for a strict positive margin:
both authentic comparison states route to the certified destination with
probability at least 1/2 at the FIRST transition. The eventual routed mass
is therefore at least 1/2. Crucially this is the original full-path
uniform constitutive margin, NOT an alternative numerical surrogate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit.SwitchWitnessMargin

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.RegimeExit
open PermanssonResearch.RegimeExit.SwitchWitnessModels
open PermanssonResearch.RegimeExit.SwitchWitnessGeometry
open PermanssonResearch.RegimeExit.SwitchWitnessExactGR
open PermanssonResearch.RegimeExit.SwitchWitnessCertificate
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization

private theorem source_singleton_outside (j : Fin 5)
    (hj : j = 2 ∨ j = 3) :
    ({decode j} : Set Y) \ sourceObservedSpec.region =
      ({decode j} : Set Y) := by
  ext z
  constructor
  · intro hz
    exact hz.1
  · intro hz
    refine ⟨hz, ?_⟩
    subst z
    rcases hj with rfl | rfl
    · simp [sourceObservedSpec, sourceSpec, decode]
    · simp [sourceObservedSpec, sourceSpec, decode]

/-- The genuine canonical first-exit event into an outside singleton on
the first transition has probability exactly its actual induced atom. -/
private theorem first_exit_singleton_at_one
    (K : RationalMarkovMatrix 5)
    (i j : Fin 5)
    (hi : decode i ∈ sourceObservedSpec.region)
    (hj : j = 2 ∨ j = 3) :
    (realizedModel K).pathLaw (Measure.dirac (decode i))
      (firstExitAtDestination sourceObservedSpec 0
        ({decode j} : Set Y)) =
    (realizedModel K).inducedKernel (decode i)
      ({decode j} : Set Y) := by
  let D : Set Y := {decode j}
  have hD : MeasurableSet D := measurableSet_singleton _
  calc
    (realizedModel K).pathLaw (Measure.dirac (decode i))
      (firstExitAtDestination sourceObservedSpec 0 D) =
        firstExitStepMass (realizedModel K) sourceObservedSpec
          0 (decode i) D := by
      exact firstExitStep_eq_pathEvent
        (realizedModel K) sourceObservedSpec 0 hi D hD
    _ = (realizedModel K).inducedKernel (decode i) D := by
      change (firstExitStepMeasure (realizedModel K) sourceObservedSpec
        0 (decode i)) D = _
      rw [firstExitStepMeasure_zero,
        exitSubkernel_apply (realizedModel K) sourceObservedSpec (decode i) hD]
      rw [source_singleton_outside j hj]

private theorem full_first_step_02 :
    fullModel.pathLaw (Measure.dirac (decode (0 : Fin 5)))
      (firstExitAtDestination sourceObservedSpec 0
        ({decode (2 : Fin 5)} : Set Y)) = (1/2 : ℝ≥0∞) := by
  rw [first_exit_singleton_at_one fullMatrix 0 2
    (by simp [sourceObservedSpec, sourceSpec, decode]) (Or.inl rfl)]
  change (realizedModel fullMatrix).inducedKernel (decode 0)
    ({decode 2} : Set Y) = _
  rw [typed_five_atom fullMatrix 0 2]
  norm_num [fullMatrix]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem full_first_step_13 :
    fullModel.pathLaw (Measure.dirac (decode (1 : Fin 5)))
      (firstExitAtDestination sourceObservedSpec 0
        ({decode (3 : Fin 5)} : Set Y)) = (1/2 : ℝ≥0∞) := by
  rw [first_exit_singleton_at_one fullMatrix 1 3
    (by simp [sourceObservedSpec, sourceSpec, decode]) (Or.inr rfl)]
  change (realizedModel fullMatrix).inducedKernel (decode 1)
    ({decode 3} : Set Y) = _
  rw [typed_five_atom fullMatrix 1 3]
  norm_num [fullMatrix]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- A single outside destination atom is an actual subset of the
destination-basin first-exit event. This is not an invariance claim. -/
private theorem singleton_exit_subset_target
    (j : Fin 5) (hj : j = 2 ∨ j = 3) :
    firstExitAtDestination sourceObservedSpec 0
        ({decode j} : Set Y) ⊆
      firstExitEverDestination sourceObservedSpec
        targetObservedSpec.basin := by
  have htarget : decode j ∈ targetObservedSpec.basin := by
    rcases hj with rfl | rfl
    · simp [targetObservedSpec, targetSpec, decode]
    · simp [targetObservedSpec, targetSpec, decode]
  intro w hw
  apply Set.mem_iUnion.mpr
  refine ⟨0, ?_⟩
  rcases hw with ⟨hs, hd⟩
  refine ⟨hs, ?_⟩
  exact ⟨by simpa only [Set.mem_singleton_iff] using
      (hd.1 ▸ htarget), hd.2⟩

private theorem half_le_routing_zero :
    (1/2 : ℝ≥0∞) ≤
      exitRoutingInfinite fullModel sourceObservedSpec
        (decode (0 : Fin 5)) targetObservedSpec.basin := by
  have hsub := singleton_exit_subset_target (2 : Fin 5) (Or.inl rfl)
  have hsource : decode (0 : Fin 5) ∈ sourceObservedSpec.region := by
    simp [sourceObservedSpec, sourceSpec, decode]
  calc
    (1/2 : ℝ≥0∞) =
        fullModel.pathLaw (Measure.dirac (decode (0 : Fin 5)))
          (firstExitAtDestination sourceObservedSpec 0
            ({decode (2 : Fin 5)} : Set Y)) := full_first_step_02.symm
    _ ≤ fullModel.pathLaw (Measure.dirac (decode (0 : Fin 5)))
        (firstExitEverDestination sourceObservedSpec
          targetObservedSpec.basin) := measure_mono hsub
    _ = exitRoutingInfinite fullModel sourceObservedSpec
          (decode (0 : Fin 5)) targetObservedSpec.basin :=
      (exitRoutingInfinite_eq_prob_exit_in fullModel sourceObservedSpec
        hsource targetObservedSpec.basin
        targetObservedSpec.basin_measurable).symm

private theorem half_le_routing_one :
    (1/2 : ℝ≥0∞) ≤
      exitRoutingInfinite fullModel sourceObservedSpec
        (decode (1 : Fin 5)) targetObservedSpec.basin := by
  have hsub := singleton_exit_subset_target (3 : Fin 5) (Or.inr rfl)
  have hsource : decode (1 : Fin 5) ∈ sourceObservedSpec.region := by
    simp [sourceObservedSpec, sourceSpec, decode]
  calc
    (1/2 : ℝ≥0∞) =
        fullModel.pathLaw (Measure.dirac (decode (1 : Fin 5)))
          (firstExitAtDestination sourceObservedSpec 0
            ({decode (3 : Fin 5)} : Set Y)) := full_first_step_13.symm
    _ ≤ fullModel.pathLaw (Measure.dirac (decode (1 : Fin 5)))
        (firstExitEverDestination sourceObservedSpec
          targetObservedSpec.basin) := measure_mono hsub
    _ = exitRoutingInfinite fullModel sourceObservedSpec
          (decode (1 : Fin 5)) targetObservedSpec.basin :=
      (exitRoutingInfinite_eq_prob_exit_in fullModel sourceObservedSpec
        hsource targetObservedSpec.basin
        targetObservedSpec.basin_measurable).symm

/-- Genuine original B1: no state outside the frozen two-point basin
is inserted to manipulate the uniform quantifier. -/
theorem full_routing_half :
    SwitchRoutingBound baselineModel sourceObservedSpec targetObservedSpec
      (researchActionFamily baselineMatrix)
      comparison fullIntervention (1/2 : ℝ≥0∞) := by
  refine ⟨by norm_num, ?_⟩
  intro y hy
  have h : y = decode (0 : Fin 5) ∨ y = decode (1 : Fin 5) := by
    rcases y with ⟨u,i⟩
    cases u
    change i = 0 ∨ i = 1 at hy
    rcases hy with h0 | h1
    · exact Or.inl (by simpa [decode] using congrArg (fun i : Fin 5 => ((),i)) h0)
    · exact Or.inr (by simpa [decode] using congrArg (fun i : Fin 5 => ((),i)) h1)
  rcases h with rfl | rfl
  · rw [show fullIntervention.intervention.apply = fullModel from
      actual_full_intervened_model]
    simpa using half_le_routing_zero
  · rw [show fullIntervention.intervention.apply = fullModel from
      actual_full_intervened_model]
    simpa using half_le_routing_one

/-- The original constitutive-margin object is uniformly at least one
half under the actually constructed, independently certified model. -/
theorem full_constitutive_margin_ge_half :
    (1/2 : ℝ) ≤ constitutiveMargin baselineModel sourceObservedSpec
      (researchActionFamily baselineMatrix)
      (switchSurvivalProperty sourceObservedSpec)
      comparison fullIntervention := by
  have h := switch_constitutive_margin_ge baselineModel sourceObservedSpec
    targetObservedSpec reference reference
    (researchActionFamily baselineMatrix) comparison fullIntervention
    certified_full_source_target (1/2 : ℝ≥0∞) full_routing_half
  norm_num at h ⊢
  exact h

end PermanssonResearch.RegimeExit.SwitchWitnessMargin
