import PermanssonResearch.Perturbation.PrimitiveProductTV

/-! A-PRIMITIVE: an actual typed row metric certificate in the bounded-diameter
profile. The metric diameter is retained explicitly. Changed physical kernels
here compare two models, rather than changing a strategic intervention's P. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Perturbation

open PermanssonLean PermanssonLean.ProbabilitySupport
open PermanssonResearch.Probability

variable {S X A : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [PseudoMetricSpace S] [PseudoMetricSpace X]
variable [MeasurableSpace.CountableOrCountablyGenerated (JointState S X) A]
variable [MeasurableSpace.CountableOrCountablyGenerated (WorldInput S X A) X]
variable [MeasurableSpace.CountableOrCountablyGenerated (UpdateInput S X A) S]

theorem inducedKernel_w1DualLE_of_primitive_product
    (M N : StrategicWorldModel S X A) {D δα δP δU : ℝ}
    (hD0 : 0 ≤ D) (hD : ∀ y z : JointState S X, dist y z ≤ D)
    (ha0 : 0 ≤ δα) (ha1 : δα ≤ 1)
    (hp0 : 0 ≤ δP) (hp1 : δP ≤ 1)
    (hu0 : 0 ≤ δU) (hu1 : δU ≤ 1)
    (ha : HasUniformEventTVBound M.generator.action N.generator.action δα)
    (hp : HasUniformEventTVBound M.world N.world δP)
    (hu : HasUniformEventTVBound M.generator.update N.generator.update δU) :
    ∀ y, W1DualLE (M.inducedKernel y) (N.inducedKernel y)
      (D * (1 - (1 - δα) * (1 - δP) * (1 - δU))) := by
  letI := StrategicWorldModel.inducedKernel_isMarkov M
  letI := StrategicWorldModel.inducedKernel_isMarkov N
  intro y
  exact (W1DualLE.of_eventTV _ _ hD0 hD).mono
    (mul_le_mul_of_nonneg_left
      (inducedKernel_tv_le_primitive_product M N ha0 ha1 hp0 hp1 hu0 hu1 ha hp hu y) hD0)

/-- The same certificate integrates against any initial probability law. -/
theorem inducedLaw_w1DualLE_of_primitive_product
    (M N : StrategicWorldModel S X A) (μ : Measure (JointState S X))
    [IsProbabilityMeasure μ] {D δα δP δU : ℝ}
    (hD0 : 0 ≤ D) (hD : ∀ y z : JointState S X, dist y z ≤ D)
    (ha0 : 0 ≤ δα) (ha1 : δα ≤ 1)
    (hp0 : 0 ≤ δP) (hp1 : δP ≤ 1)
    (hu0 : 0 ≤ δU) (hu1 : δU ≤ 1)
    (ha : HasUniformEventTVBound M.generator.action N.generator.action δα)
    (hp : HasUniformEventTVBound M.world N.world δP)
    (hu : HasUniformEventTVBound M.generator.update N.generator.update δU) :
    W1DualLE (M.inducedKernel ∘ₘ μ) (N.inducedKernel ∘ₘ μ)
      (D * (1 - (1 - δα) * (1 - δP) * (1 - δU))) := by
  letI := StrategicWorldModel.inducedKernel_isMarkov M
  letI := StrategicWorldModel.inducedKernel_isMarkov N
  exact W1DualLE.comp_of_forall μ _ _
    (inducedKernel_w1DualLE_of_primitive_product M N hD0 hD
      ha0 ha1 hp0 hp1 hu0 hu1 ha hp hu)

end PermanssonResearch.Perturbation
