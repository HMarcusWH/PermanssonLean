import PermanssonResearch.GrammarRobust.ConstantDynamics
import PermanssonResearch.GrammarRobust.BooleanPersistence
import Mathlib.Tactic

/-!
# Lane B — exact path-law OR / AND / XOR adversarial effects

These are probabilities of cylinder events under the *canonical path law* of
an actual block-intervened strategic-world model, not Boolean truth tables
postulated to be equal to the process. The infinite-path persistence theorem
is proved separately; these time-one events diagnose synergy, incomparable
causal supports and nonmonotone block effects.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust
namespace BooleanOneStepEvents

open PermanssonLean PermanssonLean.RegimeSpecification
open BooleanModel BooleanBaseline BooleanDynamics BooleanPersistence

def eventAtOne (P : Y → Prop) : Set (ℕ → Y) :=
  {w | P (w 1)}

theorem eventAtOne_measurable (P : Y → Prop) :
    MeasurableSet (eventAtOne P) := by
  change MeasurableSet ((fun w : ℕ → Y => w 1) ⁻¹' {z : Y | P z})
  exact (MeasurableSet.of_discrete).preimage (measurable_pi_apply 1)

noncomputable def propertyAtOne (P : Y → Prop) : RegimePropertyMap Y ℝ :=
  fun μ => (μ.toMeasure (eventAtOne P)).toReal

theorem propertyAtOne_eq_of_constantKernel
    (M : StrategicWorldModel Bool Bool Bool) (q : Y)
    (hK : ∀ y : Y, M.inducedKernel y = Measure.dirac q)
    (P : Y → Prop) [DecidablePred P] (y : Y) :
    propertyAtOne P (pathProbability M (diracProba y)) =
      if P q then (1 : ℝ) else 0 := by
  classical
  change ((M.pathLaw (Measure.dirac y)) (eventAtOne P)).toReal = _
  rw [ConstantDynamics.pathLaw_point_eq_dirac M q hK y]
  rw [Measure.dirac_apply' (ConstantDynamics.orbit q y)
    (eventAtOne_measurable P)]
  by_cases hp : P q
  · simp [eventAtOne, ConstantDynamics.orbit, hp]
  · simp [eventAtOne, ConstantDynamics.orbit, hp]

theorem baseline_value (P : Y → Prop) [DecidablePred P] (y : Y) :
    baselinePropertyValue (propertyAtOne P) baseline y =
      if P q0 then (1 : ℝ) else 0 := by
  exact propertyAtOne_eq_of_constantKernel baseline q0 inducedKernel_dirac P y

theorem action_value (P : Y → Prop) [DecidablePred P] (y : Y) :
    intervenedPropertyValue (propertyAtOne P)
      (admittedBlockIntervention baseline bank fine actionBlock).intervention y =
      if P actionDest then (1 : ℝ) else 0 := by
  change propertyAtOne P (pathProbability
    (admittedBlockIntervention baseline bank fine actionBlock).intervention.apply
    (diracProba y)) = _
  rw [admittedBlockIntervention_apply]
  exact propertyAtOne_eq_of_constantKernel
    (blockModel baseline bank fine actionOnly) actionDest
    actionOnly_inducedKernel P y

theorem update_value (P : Y → Prop) [DecidablePred P] (y : Y) :
    intervenedPropertyValue (propertyAtOne P)
      (admittedBlockIntervention baseline bank fine updateBlock).intervention y =
      if P updateDest then (1 : ℝ) else 0 := by
  change propertyAtOne P (pathProbability
    (admittedBlockIntervention baseline bank fine updateBlock).intervention.apply
    (diracProba y)) = _
  rw [admittedBlockIntervention_apply]
  exact propertyAtOne_eq_of_constantKernel
    (blockModel baseline bank fine updateOnly) updateDest
    updateOnly_inducedKernel P y

theorem joint_value (P : Y → Prop) [DecidablePred P] (y : Y) :
    intervenedPropertyValue (propertyAtOne P)
      (admittedBlockIntervention baseline bank fine jointBlock).intervention y =
      if P jointDest then (1 : ℝ) else 0 := by
  change propertyAtOne P (pathProbability
    (admittedBlockIntervention baseline bank fine jointBlock).intervention.apply
    (diracProba y)) = _
  rw [admittedBlockIntervention_apply]
  exact propertyAtOne_eq_of_constantKernel
    (blockModel baseline bank fine joint) jointDest
    joint_inducedKernel P y

def orP (y : Y) : Prop := y.1 = true ∨ y.2 = true
def andP (y : Y) : Prop := y.1 = true ∧ y.2 = true
def xorP (y : Y) : Prop := y.1 ≠ y.2

theorem or_pathlaw_table (y : Y) :
    baselinePropertyValue (propertyAtOne orP) baseline y = 1 ∧
    intervenedPropertyValue (propertyAtOne orP)
      (admittedBlockIntervention baseline bank fine actionBlock).intervention y = 1 ∧
    intervenedPropertyValue (propertyAtOne orP)
      (admittedBlockIntervention baseline bank fine updateBlock).intervention y = 1 ∧
    intervenedPropertyValue (propertyAtOne orP)
      (admittedBlockIntervention baseline bank fine jointBlock).intervention y = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [orP,q0] using baseline_value orP y
  · simpa [orP,actionDest] using action_value orP y
  · simpa [orP,updateDest] using update_value orP y
  · simpa [orP,jointDest] using joint_value orP y

theorem and_pathlaw_table (y : Y) :
    baselinePropertyValue (propertyAtOne andP) baseline y = 1 ∧
    intervenedPropertyValue (propertyAtOne andP)
      (admittedBlockIntervention baseline bank fine actionBlock).intervention y = 0 ∧
    intervenedPropertyValue (propertyAtOne andP)
      (admittedBlockIntervention baseline bank fine updateBlock).intervention y = 0 ∧
    intervenedPropertyValue (propertyAtOne andP)
      (admittedBlockIntervention baseline bank fine jointBlock).intervention y = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [andP,q0] using baseline_value andP y
  · simpa [andP,actionDest] using action_value andP y
  · simpa [andP,updateDest] using update_value andP y
  · simpa [andP,jointDest] using joint_value andP y

theorem xor_pathlaw_table (y : Y) :
    baselinePropertyValue (propertyAtOne xorP) baseline y = 0 ∧
    intervenedPropertyValue (propertyAtOne xorP)
      (admittedBlockIntervention baseline bank fine actionBlock).intervention y = 1 ∧
    intervenedPropertyValue (propertyAtOne xorP)
      (admittedBlockIntervention baseline bank fine updateBlock).intervention y = 1 ∧
    intervenedPropertyValue (propertyAtOne xorP)
      (admittedBlockIntervention baseline bank fine jointBlock).intervention y = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [xorP,q0] using baseline_value xorP y
  · simpa [xorP,actionDest] using action_value xorP y
  · simpa [xorP,updateDest] using update_value xorP y
  · simpa [xorP,jointDest] using joint_value xorP y

end BooleanOneStepEvents
end GrammarRobust
end PermanssonResearch
