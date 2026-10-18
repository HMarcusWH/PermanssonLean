import PermanssonResearch.Perturbation.RegenerativeCompactOccupation
import PermanssonResearch.Perturbation.RegenerativeData

/-! Literal compact-descriptor law-limit factorizations for all four
original typed full path laws. -/

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped BoundedContinuousFunction
namespace PermanssonResearch.Perturbation.RegenerativeCompactFactorization
open PermanssonLean PermanssonLean.RegimeSpecification MultipleLimit.FiniteCanonicalPath
open RegenerativeFactorization RegenerativeCompactOccupation
set_option autoImplicit false
attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov
variable {S X A V : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MetricSpace S] [MetricSpace X] [BorelSpace S] [BorelSpace X]
variable [SeparableSpace S] [SeparableSpace X] [StandardBorelSpace S] [StandardBorelSpace X]
variable [Nonempty S] [Nonempty X]
variable [MetricSpace V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V]

theorem model_property_factor (M : StrategicWorldModel S X A) (D : Data M.inducedKernel)
    {h : JointState S X → V} (hh : Continuous h) (fallback : ProbabilityMeasure V)
    (Φ : ProbabilityMeasure V →ᵇ ℝ) (y : JointState S X) :
    baselinePropertyValue (property h fallback Φ) M y = Φ (D.stationary.map h) := by
  have heq : pathProbability M (MeasureTheory.diracProba y) =
      (⟨canonicalPathLaw M.inducedKernel (Measure.dirac y),inferInstance⟩ :
        ProbabilityMeasure (ℕ → JointState S X)) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact typed_pathLaw_eq_canonical M _
  unfold baselinePropertyValue
  rw [heq]
  exact property_factor_regenerative M.inducedKernel D.residual D.seed
    (MeasureTheory.diracProba y) D.r_nonneg D.r_lt_one D.mixture hh fallback Φ

theorem four_actual_factorizations (M Mt : StrategicWorldModel S X A)
    {FType FtType : Type*} (F : InterventionFamily M FType) (Ft : InterventionFamily Mt FtType)
    (J : AdmissibleStrategicIntervention F) (Jt : AdmissibleStrategicIntervention Ft)
    (D₀ : Data M.inducedKernel) (Dₜ : Data Mt.inducedKernel)
    (DJ : Data J.intervention.apply.inducedKernel) (DJt : Data Jt.intervention.apply.inducedKernel)
    {h : JointState S X → V} (hh : Continuous h) (fallback : ProbabilityMeasure V)
    (Φ : ProbabilityMeasure V →ᵇ ℝ) (y : JointState S X) :
    baselinePropertyValue (property h fallback Φ) M y = Φ (D₀.stationary.map h) ∧
    intervenedPropertyValue (property h fallback Φ) J.intervention y = Φ (DJ.stationary.map h) ∧
    baselinePropertyValue (property h fallback Φ) Mt y = Φ (Dₜ.stationary.map h) ∧
    intervenedPropertyValue (property h fallback Φ) Jt.intervention y = Φ (DJt.stationary.map h) :=
  ⟨model_property_factor M D₀ hh fallback Φ y,
   model_property_factor J.intervention.apply DJ hh fallback Φ y,
   model_property_factor Mt Dₜ hh fallback Φ y,
   model_property_factor Jt.intervention.apply DJt hh fallback Φ y⟩

end PermanssonResearch.Perturbation.RegenerativeCompactFactorization
