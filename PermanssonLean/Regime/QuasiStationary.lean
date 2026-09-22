import PermanssonLean.Regime.Persistence
import Mathlib.Probability.Kernel.Composition.MeasureComp

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH

variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

namespace RegimeSpecification

/-- Definition 4.4a support condition for a probability law concentrated on the
regime region. -/
def IsRegionSupported
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X)) : Prop :=
  μ.toMeasure spec.region = 1

/-- Finite-persistence quasi-regime gate.  This is kept separate from the QSD
condition because the QSD eigenmeasure equation alone is not a uniform
statewise persistence statement. -/
def IsQuasiRegime
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (eta : ℝ≥0∞) : Prop :=
  IsFinitePersistent M spec L eta

/-- A quasi-stationary distribution for the killed regime dynamics.

The law is a probability measure supported on `B`, and one killed transition
scales it by the survival eigenvalue `theta`. -/
def IsQuasiStationaryDistribution
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞) : Prop :=
  IsRegionSupported spec μ ∧
  0 < theta ∧
  theta ≤ 1 ∧
  killedKernel M spec ∘ₘ μ.toMeasure = theta • μ.toMeasure

/-- A QSD-certified quasi-regime deliberately requires both the finite
persistence gate and the QSD certificate. -/
def IsQSDCertifiedQuasiRegime
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) (eta theta : ℝ≥0∞)
    (μ : ProbabilityMeasure (JointState S X)) : Prop :=
  IsQuasiRegime M spec L eta ∧
  IsQuasiStationaryDistribution M spec μ theta

theorem qsd_supported
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞)
    (hQ : IsQuasiStationaryDistribution M spec μ theta) :
    μ.toMeasure spec.region = 1 :=
  hQ.1

theorem qsd_theta_pos
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞)
    (hQ : IsQuasiStationaryDistribution M spec μ theta) :
    0 < theta :=
  hQ.2.1

theorem qsd_theta_le_one
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞)
    (hQ : IsQuasiStationaryDistribution M spec μ theta) :
    theta ≤ 1 :=
  hQ.2.2.1

theorem qsd_eigenmeasure
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞)
    (hQ : IsQuasiStationaryDistribution M spec μ theta) :
    killedKernel M spec ∘ₘ μ.toMeasure = theta • μ.toMeasure :=
  hQ.2.2.2

/-- The QSD eigenmeasure relation propagates exactly through every killed
transition: after `n` transitions, surviving mass is `theta^n μ`. -/
theorem qsd_killedMeasureIterate_eq_smul
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞)
    (hQ : IsQuasiStationaryDistribution M spec μ theta) :
    ∀ n : ℕ,
      killedMeasureIterate M spec μ.toMeasure n =
        (theta ^ n) • μ.toMeasure := by
  intro n
  induction n with
  | zero =>
      simp [killedMeasureIterate]
  | succ n ih =>
      rw [killedMeasureIterate, ih, Measure.comp_smul,
        qsd_eigenmeasure M spec μ theta hQ, smul_smul, pow_succ]

/-- Path-level surviving endpoint law under a QSD. -/
theorem qsd_survivingEndpointMeasure
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞)
    (hQ : IsQuasiStationaryDistribution M spec μ theta)
    (n : ℕ) :
    survivingEndpointMeasureFromLaw M spec μ n =
      (theta ^ n) • μ.toMeasure := by
  rw [survivingEndpointMeasureFromLaw_eq_killedMeasureIterate
      M spec μ (qsd_supported M spec μ theta hQ) n]
  exact qsd_killedMeasureIterate_eq_smul M spec μ theta hQ n

/-- Proposition 4.4b survival law: starting from a QSD, the probability of
remaining in the regime through `n` transitions is exactly `theta^n`. -/
theorem qsd_survivalProbability
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞)
    (hQ : IsQuasiStationaryDistribution M spec μ theta)
    (n : ℕ) :
    survivalProbabilityFromLaw M spec μ n = theta ^ n := by
  rw [← survivingEndpointMeasureFromLaw_univ M spec μ n,
    qsd_survivingEndpointMeasure M spec μ theta hQ n,
    Measure.smul_apply, smul_eq_mul]
  simp

/-- Normalized surviving endpoint law, i.e. the endpoint distribution
conditional on survival through the horizon. -/
noncomputable def conditionedSurvivingEndpointMeasure
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (n : ℕ) :
    Measure (JointState S X) :=
  (survivalProbabilityFromLaw M spec μ n)⁻¹ •
    survivingEndpointMeasureFromLaw M spec μ n

/-- Proposition 4.4b conditional stationarity: conditioned on survival, the
endpoint law remains the QSD at every finite horizon. -/
theorem qsd_conditionedSurvivingEndpointMeasure
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞)
    (hQ : IsQuasiStationaryDistribution M spec μ theta)
    (n : ℕ) :
    conditionedSurvivingEndpointMeasure M spec μ n = μ.toMeasure := by
  rw [conditionedSurvivingEndpointMeasure,
    qsd_survivalProbability M spec μ theta hQ n,
    qsd_survivingEndpointMeasure M spec μ theta hQ n,
    smul_smul]
  have htheta0 : theta ≠ 0 :=
    (qsd_theta_pos M spec μ theta hQ).ne'
  have hthetaTop : theta ≠ ∞ := by
    exact ne_of_lt
      (lt_of_le_of_lt (qsd_theta_le_one M spec μ theta hQ)
        ENNReal.one_lt_top)
  rw [ENNReal.inv_mul_cancel (pow_ne_zero n htheta0)
      (ENNReal.pow_ne_top hthetaTop), one_smul]

/-- Machine-checkable bundle of Proposition 4.4b's two consequences. -/
structure Proposition44bCertificate
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞) : Prop where
  survivingEndpoint :
    ∀ n : ℕ,
      survivingEndpointMeasureFromLaw M spec μ n =
        (theta ^ n) • μ.toMeasure
  survivalProbability :
    ∀ n : ℕ,
      survivalProbabilityFromLaw M spec μ n = theta ^ n
  conditionalStationarity :
    ∀ n : ℕ,
      conditionedSurvivingEndpointMeasure M spec μ n = μ.toMeasure

/-- Proposition 4.4b. -/
theorem proposition_4_4b
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞)
    (hQ : IsQuasiStationaryDistribution M spec μ theta) :
    Proposition44bCertificate M spec μ theta where
  survivingEndpoint :=
    qsd_survivingEndpointMeasure M spec μ theta hQ
  survivalProbability :=
    qsd_survivalProbability M spec μ theta hQ
  conditionalStationarity :=
    qsd_conditionedSurvivingEndpointMeasure M spec μ theta hQ

end RegimeSpecification

end PermanssonLean
