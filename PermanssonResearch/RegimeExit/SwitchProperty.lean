import PermanssonResearch.RegimeExit.SwitchRouting
import PermanssonLean.Regime.Property
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# C-Exit B — survival-property semantics

The substantive property is the real probability of survival forever in
the ORIGINAL source region, evaluated on the same full path event in the
baseline and strategically intervened models. It is not an auxiliary
descriptor or a new PR predicate.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH uT uK
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {T : Type uT}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MeasurableSpace T]
variable [TopologicalSpace S] [TopologicalSpace X]

/-- Frozen original-region all-time survival property, with the real-valued
probability convention required by the existing constitutive-margin API. -/
noncomputable def switchSurvivalProperty
    (source : RegimeSpecification (JointState S X) H) :
    RegimePropertyMap (JointState S X) ℝ :=
  fun μ => (μ.toMeasure (survivesForeverSet source)).toReal

/-- The *same* full-path functional evaluates the original baseline at one. -/
theorem switch_baseline_property_one
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    {y : JointState S X} (hy : y ∈ B₁.states) :
    baselinePropertyValue (switchSurvivalProperty source) M y = 1 := by
  change (survivalForeverProbability M source y).toReal = 1
  rw [switch_source_baseline_survival_one M source target
    mSource mTarget F B₁ J cert hy]
  norm_num

/-- Intervened evaluation is on the actual switched path law and is not
computed by inserting an arbitrary transition matrix. -/
theorem switch_intervened_property_eq_actual_survival
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (J : AdmissibleStrategicIntervention F)
    (y : JointState S X) :
    intervenedPropertyValue (switchSurvivalProperty source)
      J.intervention y =
    (survivalForeverProbability J.intervention.apply source y).toReal := by
  rfl

end PermanssonResearch.RegimeExit
