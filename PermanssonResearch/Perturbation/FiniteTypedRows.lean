import PermanssonResearch.Perturbation.FiniteSequentialCoupling
import PermanssonLean.StrategicWorld.InducedKernel
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Actual finite rows of the original typed alpha -> P -> U model.
The induced-row measure equality is proved from the original composition,
without a singleton-table certificate or an assumed lifting equivalence. -/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.Perturbation.FiniteSequential
open ActionTrace PermanssonResearch.Probability PermanssonLean
noncomputable section
variable {S X A : Type*} [Fintype S] [Fintype X] [Fintype A]
  [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
  [MeasurableSingletonClass S] [MeasurableSingletonClass X] [MeasurableSingletonClass A]

attribute [local instance] StrategicGenerator.action_isMarkov StrategicGenerator.update_isMarkov
  StrategicWorldModel.world_isMarkov StrategicWorldModel.inducedKernel_isMarkov
  StrategicWorldModel.reassociatedUpdate_isMarkov StrategicWorldModel.actionWorldKernel_isMarkov
  StrategicWorldModel.oneStepHistoryKernel_isMarkov

def actionRow (M : StrategicWorldModel S X A) (y : JointState S X) : Row A :=
  Row.ofMeasure (M.generator.action y)

def worldRow (M : StrategicWorldModel S X A) (y : JointState S X) (c : A) : Row X :=
  Row.ofMeasure (M.world (y,c))

def updateRow (M : StrategicWorldModel S X A) (y : JointState S X) (c : A) (x : X) : Row S :=
  Row.ofMeasure (M.generator.update ((y,c),x))

@[simp] theorem actionRow_measure (M : StrategicWorldModel S X A) (y : JointState S X) :
    (actionRow M y).measure=M.generator.action y := Row.ofMeasure_measure _

@[simp] theorem worldRow_measure (M : StrategicWorldModel S X A) (y : JointState S X) (c : A) :
    (worldRow M y c).measure=M.world (y,c) := Row.ofMeasure_measure _

@[simp] theorem updateRow_measure (M : StrategicWorldModel S X A) (y : JointState S X) (c : A) (x : X) :
    (updateRow M y c x).measure=M.generator.update ((y,c),x) := Row.ofMeasure_measure _

def typedRow (M : StrategicWorldModel S X A) (y : JointState S X) : Row (JointState S X) :=
  inducedRow (actionRow M y) (worldRow M y) (updateRow M y)

theorem typedRow_expect (M : StrategicWorldModel S X A) (y : JointState S X) (f : JointState S X → ℝ) :
    (typedRow M y).expect f=
      ∫ c,∫ x,∫ s,f (s,x) ∂M.generator.update ((y,c),x) ∂M.world (y,c) ∂M.generator.action y := by
  simp only [typedRow,inducedRow,Row.expect_bind,Row.expect_map]
  simp_rw [Row.expect_eq_integral,actionRow_measure,worldRow_measure,updateRow_measure]

/-- Ordinary Bochner-integral expansion of the actual frozen typed kernel. -/
theorem integral_inducedKernel_finite (M : StrategicWorldModel S X A)
    (y : JointState S X) (f : JointState S X → ℝ) :
    (∫ z,f z ∂M.inducedKernel y)=
      ∫ c,∫ x,∫ s,f (s,x) ∂M.generator.update ((y,c),x) ∂M.world (y,c) ∂M.generator.action y := by
  have hp : Measurable (fun z : (A × X) × S => (z.2,z.1.2)) := by fun_prop
  rw [StrategicWorldModel.inducedKernel,Kernel.map_apply _ hp,
    integral_map hp.aemeasurable (measurable_of_finite f).aestronglyMeasurable]
  rw [StrategicWorldModel.oneStepHistoryKernel,ProbabilityTheory.integral_compProd (Integrable.of_finite)]
  simp only [StrategicWorldModel.reassociatedUpdate,Kernel.comap_apply,
    StrategicWorldModel.updateInputReassoc]
  rw [StrategicWorldModel.actionWorldKernel,ProbabilityTheory.integral_compProd (Integrable.of_finite)]

theorem typedRow_expect_induced (M : StrategicWorldModel S X A)
    (y : JointState S X) (f : JointState S X → ℝ) :
    (typedRow M y).expect f=∫ z,f z ∂M.inducedKernel y := by
  rw [typedRow_expect,integral_inducedKernel_finite]

@[simp] theorem typedRow_measure (M : StrategicWorldModel S X A) (y : JointState S X) :
    (typedRow M y).measure=M.inducedKernel y := by
  classical
  apply Measure.ext_of_measureReal_singleton
  intro z
  have hh := typedRow_expect_induced M y (fun w => if w=z then 1 else 0)
  have htest (θ : Measure (JointState S X)) :
      (∫ w,if w=z then (1:ℝ) else 0 ∂θ)=θ.real {z} := by
    simpa [Set.indicator] using integral_indicator_one (μ:=θ) (measurableSet_singleton z)
  rw [Row.expect_eq_integral,htest,htest] at hh
  exact hh

end
end PermanssonResearch.Perturbation.FiniteSequential
