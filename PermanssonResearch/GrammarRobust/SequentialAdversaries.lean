import PermanssonResearch.GrammarRobust.SequentialBooleanBridge
import PermanssonResearch.GrammarRobust.InteractionVector
import PermanssonResearch.GrammarRobust.ConstantDynamics
import Mathlib.Tactic

/-! B2 negative witness: zero singleton infimum does NOT mean singleton
pointwise nullity.  The path property inspects Y₀ and Y₁, not invented
numeric corner values. Every model executes the original three-stage kernel. -/

open MeasureTheory ProbabilityTheory Set

namespace PermanssonResearch.GrammarRobust.SequentialAdversaries
open PermanssonLean PermanssonLean.RegimeSpecification
open SequentialEffects ConditionalMargins
open BooleanModel BooleanBaseline BooleanDynamics BooleanPersistence
open SequentialBooleanBridge

def zeroInfP (initial successor : Y) : Prop :=
  successor = jointDest ∨ (initial = q1 ∧ successor = actionDest)

instance : DecidableRel zeroInfP := by
  intro x y
  unfold zeroInfP
  infer_instance

def pairEvent : Set (ℕ → Y) :=
  {w | zeroInfP (w 0) (w 1)}

theorem pairEvent_measurable : MeasurableSet pairEvent := by
  change MeasurableSet
    ((fun w : ℕ → Y => (w 0, w 1)) ⁻¹'
      {p : Y × Y | zeroInfP p.1 p.2})
  exact MeasurableSet.of_discrete.preimage
    ((measurable_pi_apply 0).prod (measurable_pi_apply 1))

noncomputable def zeroInfProperty : RegimePropertyMap Y ℝ :=
  fun μ => (μ.toMeasure pairEvent).toReal

theorem zeroInfProperty_constant
    (M : StrategicWorldModel Bool Bool Bool) (q : Y)
    (hK : ∀ y : Y, M.inducedKernel y = Measure.dirac q) (y : Y) :
    zeroInfProperty (pathProbability M (diracProba y)) =
      if zeroInfP y q then (1 : ℝ) else 0 := by
  classical
  change ((M.pathLaw (Measure.dirac y)) pairEvent).toReal = _
  rw [ConstantDynamics.pathLaw_point_eq_dirac M q hK y]
  rw [Measure.dirac_apply' (ConstantDynamics.orbit q y) pairEvent_measurable]
  by_cases h : zeroInfP y q
  · have he : ConstantDynamics.orbit q y ∈ pairEvent := by
      simpa [pairEvent, ConstantDynamics.orbit] using h
    simp [Set.indicator, he, h]
  · have he : ConstantDynamics.orbit q y ∉ pairEvent := by
      simpa [pairEvent, ConstantDynamics.orbit] using h
    simp [Set.indicator, he, h]

theorem zeroInf_baseline (y : Y) :
    baselinePropertyValue zeroInfProperty baseline y = 0 := by
  change zeroInfProperty (pathProbability baseline (diracProba y)) = 0
  rw [zeroInfProperty_constant baseline q0 inducedKernel_dirac y]
  simp [zeroInfP, q0, jointDest, actionDest]

theorem zeroInf_action (y : Y) :
    intervenedPropertyValue zeroInfProperty
      (admittedBlockIntervention baseline bank fine actionBlock).intervention y =
      if y = q1 then (1 : ℝ) else 0 := by
  change zeroInfProperty (pathProbability
    (admittedBlockIntervention baseline bank fine actionBlock).intervention.apply
    (diracProba y)) = _
  rw [admittedBlockIntervention_apply]
  rw [zeroInfProperty_constant
    (blockModel baseline bank fine actionOnly) actionDest
    actionOnly_inducedKernel y]
  simp [zeroInfP, jointDest, actionDest]

theorem zeroInf_update (y : Y) :
    intervenedPropertyValue zeroInfProperty
      (admittedBlockIntervention baseline bank fine updateBlock).intervention y =
      0 := by
  change zeroInfProperty (pathProbability
    (admittedBlockIntervention baseline bank fine updateBlock).intervention.apply
    (diracProba y)) = 0
  rw [admittedBlockIntervention_apply]
  rw [zeroInfProperty_constant
    (blockModel baseline bank fine updateOnly) updateDest
    updateOnly_inducedKernel y]
  simp [zeroInfP, jointDest, updateDest, actionDest]

theorem zeroInf_joint (y : Y) :
    intervenedPropertyValue zeroInfProperty
      (admittedBlockIntervention baseline bank fine jointBlock).intervention y =
      1 := by
  change zeroInfProperty (pathProbability
    (admittedBlockIntervention baseline bank fine jointBlock).intervention.apply
    (diracProba y)) = 1
  rw [admittedBlockIntervention_apply]
  rw [zeroInfProperty_constant
    (blockModel baseline bank fine joint) jointDest joint_inducedKernel y]
  simp [zeroInfP]

theorem zeroInf_joint_effect_one (y : Y) :
    jointEffect booleanCorners zeroInfProperty y = 1 := by
  change dist (baselinePropertyValue zeroInfProperty baseline y)
    (intervenedPropertyValue zeroInfProperty
      (admittedBlockIntervention baseline bank fine jointBlock).intervention y) = 1
  rw [zeroInf_baseline, zeroInf_joint]
  norm_num

theorem zeroInf_action_effect_q0 :
    actionEffect booleanCorners zeroInfProperty q0 = 0 := by
  change dist (baselinePropertyValue zeroInfProperty baseline q0)
    (intervenedPropertyValue zeroInfProperty
      (admittedBlockIntervention baseline bank fine actionBlock).intervention q0) = 0
  rw [zeroInf_baseline, zeroInf_action]
  simp [q0, q1]

theorem zeroInf_action_effect_q1 :
    actionEffect booleanCorners zeroInfProperty q1 = 1 := by
  change dist (baselinePropertyValue zeroInfProperty baseline q1)
    (intervenedPropertyValue zeroInfProperty
      (admittedBlockIntervention baseline bank fine actionBlock).intervention q1) = 1
  rw [zeroInf_baseline, zeroInf_action]
  simp

theorem zeroInf_update_effect_zero (y : Y) :
    updateEffect booleanCorners zeroInfProperty y = 0 := by
  change dist (baselinePropertyValue zeroInfProperty baseline y)
    (intervenedPropertyValue zeroInfProperty
      (admittedBlockIntervention baseline bank fine updateBlock).intervention y) = 0
  rw [zeroInf_baseline, zeroInf_update]
  simp

end PermanssonResearch.GrammarRobust.SequentialAdversaries
