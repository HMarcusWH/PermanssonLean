import PermanssonResearch.MultipleLimit.FiniteObservedEventMass
import PermanssonLean.Regime.UniformPermansson
import Mathlib.Tactic

/-!
# C7-03 — real typed response for a fixed eventual Boolean event

The baseline and intervened induced kernels receive SEPARATE recurrent
decompositions, selectors and exact class weights. The world primitive
P is held fixed by the existing admissible strategic-intervention type.
No second post-hoc observation or baseline-selector transfer occurs.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedObservedEventConstitution

-- A misspelled or unresolved declaration must never become an implicit theorem premise.
set_option autoImplicit false

open PermanssonLean
open PermanssonLean.RegimeSpecification
open FiniteCanonicalPath
open FiniteObservedClassSupport
open FiniteObservedEventMass
open FrozenObservedEvent
open CanonicalClassSelector

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable [DecidableEq Y] [StandardBorelSpace Y]

/-- A point-started, kernel-specific, exact ENNReal good-class mass.
One must NEVER substitute a class selector belonging to another K. -/
noncomputable def pointGoodMass
    (K : Kernel Y Y) [IsMarkovKernel K] (h : Y → Bool)
    (y : Y) : ℝ≥0∞ :=
  ∑ i ∈ goodRecurrentRepresentatives K h,
    (canonicalPathLaw K (Measure.dirac y))
      ((selectedRepresentative K) ⁻¹' ({i} : Set Y))

theorem pointGoodMass_eq_event_probability
    (K : Kernel Y Y) [IsMarkovKernel K]
    (h : Y → Bool) (y : Y) :
    pointGoodMass K h y =
      (canonicalPathLaw K (Measure.dirac y))
        (eventuallyObserved h true) := by
  exact (eventuallyObserved_probability_eq_good_sum
    K h (diracProba y)).symm

variable {S X A H : Type*}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace A] [MeasurableSpace H]
variable [TopologicalSpace S] [TopologicalSpace X]
variable [Fintype (JointState S X)] [Nonempty (JointState S X)]
variable [DecidableEq (JointState S X)]
variable [MeasurableSingletonClass (JointState S X)]
variable [StandardBorelSpace (JointState S X)]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- Exact original property on the TRUE baseline typed infinite paths,
computed by the baseline kernel's own finite class-selection weights. -/
theorem baselineValue_eq_goodMass
    (M : StrategicWorldModel S X A)
    (h : JointState S X → Bool) (y : JointState S X) :
    baselinePropertyValue
      (eventuallyObservedProperty h true) M y =
      (pointGoodMass M.inducedKernel h y).toReal := by
  change ((M.pathLaw (Measure.dirac y))
    (eventuallyObserved h true)).toReal = _
  rw [typed_pathLaw_eq_canonical M (Measure.dirac y)]
  exact congrArg ENNReal.toReal
    (pointGoodMass_eq_event_probability M.inducedKernel h y).symm

/-- The typed intervention uses its ACTUAL intervened induced kernel
and its own recurrent-class selection; P remains fixed by typing. -/
theorem intervenedValue_eq_goodMass
    (M : StrategicWorldModel S X A)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (J : AdmissibleStrategicIntervention F)
    (h : JointState S X → Bool) (y : JointState S X) :
    intervenedPropertyValue (eventuallyObservedProperty h true)
      J.intervention y =
      (pointGoodMass J.intervention.apply.inducedKernel h y).toReal := by
  change ((J.intervention.apply.pathLaw (Measure.dirac y))
    (eventuallyObserved h true)).toReal = _
  rw [typed_pathLaw_eq_canonical J.intervention.apply (Measure.dirac y)]
  exact congrArg ENNReal.toReal
    (pointGoodMass_eq_event_probability
      J.intervention.apply.inducedKernel h y).symm

/-- Exact original pointwise constitution gap, not a newly defined
weaker effect and not a comparison of transient observed marginals. -/
theorem effect_eq_abs_goodMass_difference
    (M : StrategicWorldModel S X A)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (J : AdmissibleStrategicIntervention F)
    (h : JointState S X → Bool) (y : JointState S X) :
    constitutiveEffect M (eventuallyObservedProperty h true) J y =
      |(pointGoodMass M.inducedKernel h y).toReal -
        (pointGoodMass J.intervention.apply.inducedKernel h y).toReal| := by
  unfold constitutiveEffect
  rw [baselineValue_eq_goodMass M h y,
      intervenedValue_eq_goodMass M F J h y]
  exact Real.dist_eq

end TypedObservedEventConstitution
end MultipleLimit
end PermanssonResearch
