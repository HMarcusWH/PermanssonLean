import PermanssonLean.Regime.RepresentationEquivalence
import PermanssonLean.Regime.ConstitutiveMargin
import PermanssonLean.Regime.Permansson
import PermanssonLean.Regime.Persistence
import Mathlib.Probability.Kernel.Deterministic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonLean

/-!
# Section 7 constitutive non-invariance counterexample

This file formalizes Theorem 7.3 from Permansson v0.1.7 by an explicit finite
typed witness.  The manuscript gives a Bernoulli-1/2 example; the Lean proof
uses an equivalent deterministic finite witness so the theorem is checked
without importing an unrelated law-of-large-numbers development.

The two models have the same baseline induced joint kernel and therefore the
same Exact-GR status.  The same action-selection replacement leaves one model
unchanged but changes the other model's world dynamics.  A frozen path property
then witnesses non-constitution in the first representation and uniform
constitution in the second.
-/

namespace Section7ConstitutiveNoninvariance

noncomputable section

/-- Baseline action for representation A: always false. -/
def actionFalse : Kernel (JointState Bool Bool) Bool :=
  Kernel.deterministic (fun _ => false) (by exact Measurable.of_discrete)

/-- Baseline action for representation B: always true. -/
def actionTrue : Kernel (JointState Bool Bool) Bool :=
  Kernel.deterministic (fun _ => true) (by exact Measurable.of_discrete)

/-- Strategic memory is preserved exactly. -/
def updatePreserve : Kernel (UpdateInput Bool Bool Bool) Bool :=
  Kernel.deterministic (fun z => z.1.1.1) (by exact Measurable.of_discrete)

/-- Representation A's world kernel ignores the action and preserves x. -/
def worldA : Kernel (WorldInput Bool Bool Bool) Bool :=
  Kernel.deterministic (fun z => z.1.2) (by exact Measurable.of_discrete)

/-- Representation B preserves x under its baseline action true, but sends the
world bit to true under the diagnostic action false. -/
def worldB : Kernel (WorldInput Bool Bool Bool) Bool :=
  Kernel.deterministic
    (fun z => if z.2 then z.1.2 else true)
    (by exact Measurable.of_discrete)

def generatorA : StrategicGenerator Bool Bool Bool where
  action := actionFalse
  update := updatePreserve
  action_isMarkov := by
    unfold actionFalse
    infer_instance
  update_isMarkov := by
    unfold updatePreserve
    infer_instance

def generatorB : StrategicGenerator Bool Bool Bool where
  action := actionTrue
  update := updatePreserve
  action_isMarkov := by
    unfold actionTrue
    infer_instance
  update_isMarkov := by
    unfold updatePreserve
    infer_instance

def modelA : StrategicWorldModel Bool Bool Bool where
  generator := generatorA
  world := worldA
  world_isMarkov := by
    unfold worldA
    infer_instance

def modelB : StrategicWorldModel Bool Bool Bool where
  generator := generatorB
  world := worldB
  world_isMarkov := by
    unfold worldB
    infer_instance

/-- Both baseline factorizations induce the identity dynamics on the joint
strategic/world state. -/
theorem baseline_inducedKernel_eq :
    modelA.inducedKernel = modelB.inducedKernel := by
  ext y E hE
  rw [StrategicWorldModel.inducedKernel_apply modelA y hE,
      StrategicWorldModel.inducedKernel_apply modelB y hE]
  rcases y with ⟨s, x⟩
  cases s <;> cases x <;>
    simp [modelA, modelB, generatorA, generatorB,
      actionFalse, actionTrue, updatePreserve, worldA, worldB,
      Kernel.deterministic_apply]

/-- Frozen custom convergence mode used only to isolate the representation
claim of Theorem 7.3 from independent asymptotic machinery. -/
def witnessConvergenceMode :
    ConvergenceMode (JointState Bool Bool) Bool :=
  ConvergenceMode.custom _ _ (fun _ _ _ => True)

/-- Regime region is the whole finite state space.  The comparison basin fixes
x=false but contains two distinct strategic-memory states. -/
def regimeSpec : RegimeSpecification (JointState Bool Bool) Bool where
  region := Set.univ
  region_measurable := MeasurableSet.univ
  basin := {y | y.2 = false}
  basin_measurable := by
    exact (measurable_snd : Measurable fun y : JointState Bool Bool => y.2)
      (measurableSet_singleton false)
  basin_subset_region := by
    intro y hy
    simp
  descriptor := fun y => y.2
  descriptor_measurable := measurable_snd
  target := ⟨Measure.dirac false, inferInstance⟩
  convergenceMode := witnessConvergenceMode

/-- Auxiliary survival specification for the property map: remain in x=false
through one transition. -/
def stayFalseSpec : RegimeSpecification (JointState Bool Bool) Unit where
  region := {y | y.2 = false}
  region_measurable := by
    exact (measurable_snd : Measurable fun y : JointState Bool Bool => y.2)
      (measurableSet_singleton false)
  basin := {y | y.2 = false}
  basin_measurable := by
    exact (measurable_snd : Measurable fun y : JointState Bool Bool => y.2)
      (measurableSet_singleton false)
  basin_subset_region := by
    intro y hy
    exact hy
  descriptor := fun _ => ()
  descriptor_measurable := measurable_const
  target := ⟨Measure.dirac (), inferInstance⟩
  convergenceMode := ConvergenceMode.custom _ _ (fun _ _ _ => True)

/-- Reference measure for the finite Exact-GR witness. -/
def referenceMeasure : Measure (JointState Bool Bool) :=
  Measure.dirac (false, false)

/-- Assumption 4.1 for the finite witness. -/
theorem assumption41_modelA :
    RegimeSpecification.Assumption41 modelA regimeSpec referenceMeasure := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨(false, false), by simp [regimeSpec]⟩
  · left
    simp [RegimeSpecification.RegionNontrivial, regimeSpec]
  · exact ⟨(false, false), by simp [regimeSpec],
      (false, true), by simp [regimeSpec], by simp [regimeSpec]⟩
  · apply RegimeSpecification.two_states_implies_basinPathLawNontrivial
    exact ⟨(false, false), by simp [regimeSpec],
      (true, false), by simp [regimeSpec], by simp⟩

theorem exactlyInvariant_modelA :
    RegimeSpecification.IsExactlyInvariant modelA regimeSpec := by
  intro y hy
  letI : IsMarkovKernel modelA.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov modelA
  simp [regimeSpec]

/-- Representation A is an Exact GR under the frozen witness specification. -/
theorem exactGR_modelA :
    RegimeSpecification.IsExactGeneratedRegime
      modelA regimeSpec referenceMeasure := by
  refine ⟨RegimeSpecification.canonicalProcessWellPosed modelA,
    assumption41_modelA, exactlyInvariant_modelA, ?_⟩
  intro initLaw hinit
  simp [RegimeSpecification.IsLimitingOccupationLaw,
    regimeSpec, witnessConvergenceMode, ConvergenceMode.custom]

/-- Equal baseline induced kernels transport Exact-GR status to representation B. -/
theorem exactGR_modelB :
    RegimeSpecification.IsExactGeneratedRegime
      modelB regimeSpec referenceMeasure := by
  exact
    (RegimeSpecification.exactGR_iff_of_inducedKernel_eq
      modelA modelB baseline_inducedKernel_eq regimeSpec referenceMeasure).1
      exactGR_modelA

end

end Section7ConstitutiveNoninvariance

end PermanssonLean
