import PermanssonResearch.Perturbation.RegenerativeOccupationProperty
import PermanssonResearch.Perturbation.RegenerativeData

/-! All four original typed path laws, with the same predeclared descriptor,
numeric limit functional and fallback, and the original full margin theorem. -/

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped NNReal BoundedContinuousFunction
namespace PermanssonResearch.Perturbation.RegenerativeFactorization
open PermanssonLean PermanssonLean.RegimeSpecification MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.Probability
open RegenerativeOccupationProperty
set_option autoImplicit false
attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

variable {S X A V : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MetricSpace S] [MetricSpace X] [BorelSpace S] [BorelSpace X]
variable [SeparableSpace S] [SeparableSpace X] [StandardBorelSpace S] [StandardBorelSpace X]
variable [Nonempty S] [Nonempty X]
variable [MetricSpace V] [MeasurableSpace V] [BorelSpace V] [SeparableSpace V]

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

theorem generated_occupationMargin_robust
    {H Ht : Type*} [MeasurableSpace H] [MeasurableSpace Ht]
    (M Mt : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (spect : RegimeSpecification (JointState S X) Ht)
    {FType FtType : Type*} (F : InterventionFamily M FType) (Ft : InterventionFamily Mt FtType)
    (J : AdmissibleStrategicIntervention F) (Jt : AdmissibleStrategicIntervention Ft)
    (B : ConstitutiveComparisonSet M spec) (Bt : ConstitutiveComparisonSet Mt spect)
    (hB : Bt.states = B.states)
    (D₀ : Data M.inducedKernel) (Dₜ : Data Mt.inducedKernel)
    (DJ : Data J.intervention.apply.inducedKernel) (DJt : Data Jt.intervention.apply.inducedKernel)
    (y₀ : JointState S X)
    (hπ₀ : Integrable (fun y => dist y y₀) D₀.stationary.toMeasure)
    (hπₜ : Integrable (fun y => dist y y₀) Dₜ.stationary.toMeasure)
    (hπJ : Integrable (fun y => dist y y₀) DJ.stationary.toMeasure)
    (hπJt : Integrable (fun y => dist y y₀) DJt.stationary.toMeasure)
    {ρ₀ ρJ δ₀ δJ : ℝ} (hρ₀0 : 0 ≤ ρ₀) (hρ₀1 : ρ₀ < 1)
    (hρJ0 : 0 ≤ ρJ) (hρJ1 : ρJ < 1)
    (hK₀ : IsW1Contraction M.inducedKernel ρ₀)
    (hKJ : IsW1Contraction J.intervention.apply.inducedKernel ρJ)
    (hδ₀ : ∀ y, W1DualLE (M.inducedKernel y) (Mt.inducedKernel y) δ₀)
    (hδJ : ∀ y, W1DualLE (J.intervention.apply.inducedKernel y)
      (Jt.intervention.apply.inducedKernel y) δJ)
    (h : JointState S X → V) {Lh : ℝ≥0} (hLh : LipschitzWith Lh h)
    (fallback : ProbabilityMeasure V) (Φ : Measure V → ℝ)
    (Φb : ProbabilityMeasure V →ᵇ ℝ) (hΦb : ∀ ν, Φb ν = Φ ν.toMeasure)
    {LF : ℝ} (hΦ : IsW1LipschitzFunctional Φ LF) :
    |constitutiveMargin Mt spect Ft (property h fallback Φb) Bt Jt -
      constitutiveMargin M spec F (property h fallback Φb) B J| ≤
      LF * Lh * (δ₀/(1-ρ₀)+δJ/(1-ρJ)) := by
  let P₀ := generatedPerturbation M.inducedKernel Mt.inducedKernel D₀ Dₜ y₀
    hπ₀ hπₜ hρ₀0 hρ₀1 hK₀ hδ₀
  let PJ := generatedPerturbation J.intervention.apply.inducedKernel
    Jt.intervention.apply.inducedKernel DJ DJt y₀ hπJ hπJt hρJ0 hρJ1 hKJ hδJ
  apply occupationMargin_robust M Mt spec spect F Ft (property h fallback Φb)
    B Bt hB J Jt P₀ PJ hLh.continuous.measurable hLh hΦ
  intro y hy
  have he := four_actual_factorizations M Mt F Ft J Jt D₀ Dₜ DJ DJt
    hLh.continuous fallback Φb y
  simpa only [hΦb,ProbabilityMeasure.toMeasure_map,P₀,PJ,generatedPerturbation] using! he

end PermanssonResearch.Perturbation.RegenerativeFactorization
