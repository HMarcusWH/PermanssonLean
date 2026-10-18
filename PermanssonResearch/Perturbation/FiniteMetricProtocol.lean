import PermanssonResearch.Perturbation.FiniteStateMetricContraction
import PermanssonResearch.Perturbation.FiniteOccupationFactorization
import PermanssonResearch.Perturbation.PrimitiveModelPair

/-! Four actual typed-kernel certificates for a matched original intervention
protocol. Primitive inequalities generate contraction, invariant laws, the
four occupation-property factorizations, and the unchanged original margin
bound. Strictness is an explicit numeric inequality for every actual kernel. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace PermanssonResearch.Perturbation.FiniteSequential
open PermanssonLean PermanssonLean.RegimeSpecification PermanssonResearch.Probability
open FiniteOccupationFactorization FiniteOccupationProperty
noncomputable section
variable {S X A : Type*} [Fintype S] [Fintype X] [Fintype A]
  [Nonempty S] [Nonempty X] [Nonempty A]
  [MetricSpace S] [MetricSpace X] [PseudoMetricSpace A]
  [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
  [MeasurableSingletonClass S] [MeasurableSingletonClass X] [MeasurableSingletonClass A]
attribute [local instance] StrategicWorldModel.inducedKernel_isMarkov

structure MetricProtocolBounds (M : StrategicWorldModel S X A) {Component : Type*}
    (F : InterventionFamily M Component) (J : AdmissibleStrategicIntervention F)
    (pair : PrimitiveModelPair M F J) where
  strategicWeight : ℝ≥0
  worldWeight : ℝ≥0
  strategic_pos : 0<(strategicWeight:ℝ)
  world_pos : 0<(worldWeight:ℝ)
  baseline : StateMetricBounds M (fun y z => dist y z)
  approximate : StateMetricBounds pair.approximate (fun y z => dist y z)
  intervention : StateMetricBounds J.intervention.apply (fun y z => dist y z)
  approximateIntervention : StateMetricBounds pair.approximateIntervention.intervention.apply (fun y z => dist y z)
  baselineError : PrimitiveMetricBounds M pair.approximate
  interventionError : PrimitiveMetricBounds J.intervention.apply pair.approximateIntervention.intervention.apply
  baseline_strict : baseline.factor strategicWeight worldWeight/min (strategicWeight:ℝ) (worldWeight:ℝ)<1
  approximate_strict : approximate.factor strategicWeight worldWeight/min (strategicWeight:ℝ) (worldWeight:ℝ)<1
  intervention_strict : intervention.factor strategicWeight worldWeight/min (strategicWeight:ℝ) (worldWeight:ℝ)<1
  approximateIntervention_strict : approximateIntervention.factor strategicWeight worldWeight/
    min (strategicWeight:ℝ) (worldWeight:ℝ)<1

variable {M : StrategicWorldModel S X A} {Component : Type*}
  {F : InterventionFamily M Component} {J : AdmissibleStrategicIntervention F}
  {pair : PrimitiveModelPair M F J}

def MetricProtocolBounds.rho0 (D : MetricProtocolBounds M F J pair) : ℝ :=
  D.baseline.factor D.strategicWeight D.worldWeight/min (D.strategicWeight:ℝ) (D.worldWeight:ℝ)

def MetricProtocolBounds.rhoJ (D : MetricProtocolBounds M F J pair) : ℝ :=
  D.intervention.factor D.strategicWeight D.worldWeight/min (D.strategicWeight:ℝ) (D.worldWeight:ℝ)

def MetricProtocolBounds.delta0 (D : MetricProtocolBounds M F J pair) : ℝ :=
  D.baselineError.budget D.strategicWeight D.worldWeight/min (D.strategicWeight:ℝ) (D.worldWeight:ℝ)

def MetricProtocolBounds.deltaJ (D : MetricProtocolBounds M F J pair) : ℝ :=
  D.interventionError.budget D.strategicWeight D.worldWeight/min (D.strategicWeight:ℝ) (D.worldWeight:ℝ)

def MetricProtocolBounds.baselineData (D : MetricProtocolBounds M F J pair) :
    ClassPerturbationData M.inducedKernel pair.approximate.inducedKernel :=
  dataOfBothContractions _ _
    (div_nonneg (D.baseline.factor_nonneg _ _) (lt_min D.strategic_pos D.world_pos).le)
    D.baseline_strict
    (D.baseline.original_isW1Contraction _ _ D.strategic_pos D.world_pos)
    (div_nonneg (D.approximate.factor_nonneg _ _) (lt_min D.strategic_pos D.world_pos).le)
    D.approximate_strict
    (D.approximate.original_isW1Contraction _ _ D.strategic_pos D.world_pos)
    (D.baselineError.original_induced_bound _ _ D.strategic_pos D.world_pos)

def MetricProtocolBounds.interventionData (D : MetricProtocolBounds M F J pair) :
    ClassPerturbationData J.intervention.apply.inducedKernel
      pair.approximateIntervention.intervention.apply.inducedKernel :=
  dataOfBothContractions _ _
    (div_nonneg (D.intervention.factor_nonneg _ _) (lt_min D.strategic_pos D.world_pos).le)
    D.intervention_strict
    (D.intervention.original_isW1Contraction _ _ D.strategic_pos D.world_pos)
    (div_nonneg (D.approximateIntervention.factor_nonneg _ _) (lt_min D.strategic_pos D.world_pos).le)
    D.approximateIntervention_strict
    (D.approximateIntervention.original_isW1Contraction _ _ D.strategic_pos D.world_pos)
    (D.interventionError.original_induced_bound _ _ D.strategic_pos D.world_pos)

theorem MetricProtocolBounds.baseline_invariant_gap (D : MetricProtocolBounds M F J pair) :
    W1DualLE D.baselineData.generated.π D.baselineData.generated.πt (D.delta0/(1-D.rho0)) :=
  D.baselineData.generated.w1_le

theorem MetricProtocolBounds.intervention_invariant_gap (D : MetricProtocolBounds M F J pair) :
    W1DualLE D.interventionData.generated.π D.interventionData.generated.πt (D.deltaJ/(1-D.rhoJ)) :=
  D.interventionData.generated.w1_le

variable [DecidableEq S] [DecidableEq X]
  [OpensMeasurableSpace S] [OpensMeasurableSpace X]
  [StandardBorelSpace S] [StandardBorelSpace X]

/-- The original complete comparison set and matched intervention labels
are retained. All four hfac components come from actual finite occupation
convergence, and both invariant pairs are generated rather than assumed. -/
theorem MetricProtocolBounds.original_occupationMargin
    {H V : Type*} [MeasurableSpace H]
    [MetricSpace V] [MeasurableSpace V] [BorelSpace V] [Fintype V]
    (D : MetricProtocolBounds M F J pair)
    (spec : RegimeSpecification (JointState S X) H) (B : ConstitutiveComparisonSet M spec)
    (h : JointState S X → V) (hh : Measurable h) {Lh : ℝ≥0} (hLh : LipschitzWith Lh h)
    (fallback : ProbabilityMeasure V) (Φ : Measure V → ℝ)
    (hcont : Continuous (fun q : ProbabilityMeasure V => Φ q.toMeasure))
    {LF : ℝ} (hΦ : IsW1LipschitzFunctional Φ LF) :
    |constitutiveMargin pair.approximate spec pair.approximateFamily
        (property h fallback ⟨_,hcont⟩) (pair.comparisonSet spec B) pair.approximateIntervention-
      constitutiveMargin M spec F (property h fallback ⟨_,hcont⟩) B J|≤
      LF*Lh*(D.delta0/(1-D.rho0)+D.deltaJ/(1-D.rhoJ)) :=
  generated_occupationMargin_robust M pair.approximate spec spec F pair.approximateFamily
    J pair.approximateIntervention B (pair.comparisonSet spec B) rfl
    D.baselineData D.interventionData h hh hLh fallback Φ hcont hΦ

end
end PermanssonResearch.Perturbation.FiniteSequential
