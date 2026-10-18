import PermanssonResearch.MultipleLimit.RegenerativeFirstMomentOccupation
import PermanssonResearch.Perturbation.RegenerativeData

/-! The original four typed path-law factorizations and full constitutive
margin, using a fixed genuine P1 occupation-limit property. State and
descriptor moments follow from explicit regenerative reward conditions. -/

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped NNReal BoundedContinuousFunction
namespace PermanssonResearch.Perturbation.RegenerativeMomentFactorization
open PermanssonLean PermanssonLean.RegimeSpecification
open MultipleLimit.FiniteCanonicalPath PermanssonResearch.Probability
open RegenerativeFactorization FirstMomentOccupation
set_option autoImplicit false
attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

variable {S X A V : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MetricSpace S] [MetricSpace X] [BorelSpace S] [BorelSpace X]
variable [SeparableSpace S] [SeparableSpace X] [StandardBorelSpace S] [StandardBorelSpace X]
variable [Nonempty S] [Nonempty X]
variable [MetricSpace V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
variable [SeparableSpace V] [Nonempty V]

def StateBudget {K : Kernel (JointState S X) (JointState S X)} (D : Data K)
    (y₀ : JointState S X) : Prop :=
  RegenerativeMoment.RewardCondition D.residual D.seed D.r (fun y => dist y y₀)

def DescriptorBudget {K : Kernel (JointState S X) (JointState S X)} (D : Data K)
    (h : JointState S X → V) (v₀ : V) : Prop :=
  RegenerativeMoment.RewardCondition D.residual D.seed D.r (fun y => dist (h y) v₀)

theorem stateMoment {K : Kernel (JointState S X) (JointState S X)} (D : Data K)
    (y₀ : JointState S X) (hbudget : StateBudget D y₀) :
    Integrable (fun y => dist y y₀) D.stationary.toMeasure :=
  RegenerativeMoment.integrable_law_of_rewardCondition D.residual D.seed
    D.r_nonneg D.r_lt_one (measurable_id.dist measurable_const) hbudget

noncomputable def descriptorTarget {K : Kernel (JointState S X) (JointState S X)} (D : Data K)
    (h : JointState S X → V) (hh : Measurable h) (v₀ : V) (hbudget : DescriptorBudget D h v₀) :
    FirstMomentProbability v₀ :=
  MultipleLimit.RegenerativeDescriptorMoments.target D.residual D.seed D.r_nonneg D.r_lt_one
    h hh v₀ hbudget

theorem descriptorTarget_measure {K : Kernel (JointState S X) (JointState S X)} (D : Data K)
    (h : JointState S X → V) (hh : Measurable h) (v₀ : V) (hbudget : DescriptorBudget D h v₀) :
    (descriptorTarget D h hh v₀ hbudget).measure = D.stationary.toMeasure.map h := rfl

theorem model_property_factor (M : StrategicWorldModel S X A) (D : Data M.inducedKernel)
    (h : JointState S X → V) (hh : Measurable h) (v₀ : V) (hbudget : DescriptorBudget D h v₀)
    (fallback : FirstMomentProbability v₀) (Φ : FirstMomentProbability v₀ →ᵇ ℝ)
    (y : JointState S X) :
    baselinePropertyValue (property v₀ h fallback Φ) M y = Φ (descriptorTarget D h hh v₀ hbudget) := by
  have heq : pathProbability M (MeasureTheory.diracProba y) =
      (⟨canonicalPathLaw M.inducedKernel (Measure.dirac y),inferInstance⟩ :
        ProbabilityMeasure (ℕ → JointState S X)) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact typed_pathLaw_eq_canonical M _
  unfold baselinePropertyValue
  rw [heq]
  exact MultipleLimit.RegenerativeFirstMoment.canonical_property_factor D.residual M.inducedKernel
    D.seed (MeasureTheory.diracProba y) D.r_nonneg D.r_lt_one D.mixture
    h hh v₀ hbudget fallback Φ

theorem four_actual_factorizations (M Mt : StrategicWorldModel S X A)
    {FType FtType : Type*} (F : InterventionFamily M FType) (Ft : InterventionFamily Mt FtType)
    (J : AdmissibleStrategicIntervention F) (Jt : AdmissibleStrategicIntervention Ft)
    (D₀ : Data M.inducedKernel) (Dₜ : Data Mt.inducedKernel)
    (DJ : Data J.intervention.apply.inducedKernel) (DJt : Data Jt.intervention.apply.inducedKernel)
    (h : JointState S X → V) (hh : Measurable h) (v₀ : V)
    (hb₀ : DescriptorBudget D₀ h v₀) (hbₜ : DescriptorBudget Dₜ h v₀)
    (hbJ : DescriptorBudget DJ h v₀) (hbJt : DescriptorBudget DJt h v₀)
    (fallback : FirstMomentProbability v₀) (Φ : FirstMomentProbability v₀ →ᵇ ℝ)
    (y : JointState S X) :
    baselinePropertyValue (property v₀ h fallback Φ) M y = Φ (descriptorTarget D₀ h hh v₀ hb₀) ∧
    intervenedPropertyValue (property v₀ h fallback Φ) J.intervention y = Φ (descriptorTarget DJ h hh v₀ hbJ) ∧
    baselinePropertyValue (property v₀ h fallback Φ) Mt y = Φ (descriptorTarget Dₜ h hh v₀ hbₜ) ∧
    intervenedPropertyValue (property v₀ h fallback Φ) Jt.intervention y = Φ (descriptorTarget DJt h hh v₀ hbJt) :=
  ⟨model_property_factor M D₀ h hh v₀ hb₀ fallback Φ y,
   model_property_factor J.intervention.apply DJ h hh v₀ hbJ fallback Φ y,
   model_property_factor Mt Dₜ h hh v₀ hbₜ fallback Φ y,
   model_property_factor Jt.intervention.apply DJt h hh v₀ hbJt fallback Φ y⟩

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
    (hs₀ : StateBudget D₀ y₀) (hsₜ : StateBudget Dₜ y₀)
    (hsJ : StateBudget DJ y₀) (hsJt : StateBudget DJt y₀)
    {ρ₀ ρJ δ₀ δJ : ℝ} (hρ₀0 : 0 ≤ ρ₀) (hρ₀1 : ρ₀ < 1)
    (hρJ0 : 0 ≤ ρJ) (hρJ1 : ρJ < 1)
    (hK₀ : IsW1Contraction M.inducedKernel ρ₀)
    (hKJ : IsW1Contraction J.intervention.apply.inducedKernel ρJ)
    (hδ₀ : ∀ y, W1DualLE (M.inducedKernel y) (Mt.inducedKernel y) δ₀)
    (hδJ : ∀ y, W1DualLE (J.intervention.apply.inducedKernel y)
      (Jt.intervention.apply.inducedKernel y) δJ)
    (h : JointState S X → V) {Lh : ℝ≥0} (hLh : LipschitzWith Lh h) (v₀ : V)
    (hb₀ : DescriptorBudget D₀ h v₀) (hbₜ : DescriptorBudget Dₜ h v₀)
    (hbJ : DescriptorBudget DJ h v₀) (hbJt : DescriptorBudget DJt h v₀)
    (fallback : FirstMomentProbability v₀) (Φ : Measure V → ℝ)
    (Φb : FirstMomentProbability v₀ →ᵇ ℝ) (hΦb : ∀ ν, Φb ν = Φ ν.measure)
    {LF : ℝ} (hΦ : IsW1LipschitzFunctional Φ LF) :
    |constitutiveMargin Mt spect Ft (property v₀ h fallback Φb) Bt Jt -
      constitutiveMargin M spec F (property v₀ h fallback Φb) B J| ≤
      LF * Lh * (δ₀/(1-ρ₀)+δJ/(1-ρJ)) := by
  let P₀ := generatedPerturbation M.inducedKernel Mt.inducedKernel D₀ Dₜ y₀
    (stateMoment D₀ y₀ hs₀) (stateMoment Dₜ y₀ hsₜ) hρ₀0 hρ₀1 hK₀ hδ₀
  let PJ := generatedPerturbation J.intervention.apply.inducedKernel
    Jt.intervention.apply.inducedKernel DJ DJt y₀
    (stateMoment DJ y₀ hsJ) (stateMoment DJt y₀ hsJt) hρJ0 hρJ1 hKJ hδJ
  apply occupationMargin_robust M Mt spec spect F Ft (property v₀ h fallback Φb)
    B Bt hB J Jt P₀ PJ hLh.continuous.measurable hLh hΦ
  intro y hy
  have he := four_actual_factorizations M Mt F Ft J Jt D₀ Dₜ DJ DJt h hLh.continuous.measurable
    v₀ hb₀ hbₜ hbJ hbJt fallback Φb y
  simpa only [hΦb,descriptorTarget_measure,P₀,PJ,generatedPerturbation] using! he

end PermanssonResearch.Perturbation.RegenerativeMomentFactorization
