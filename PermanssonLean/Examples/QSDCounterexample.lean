import PermanssonLean.Regime.QuasiStationary
import Mathlib.Probability.Kernel.Deterministic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonLean

open RegimeSpecification

/-!
# QSD does not imply uniform finite persistence

This finite witness records the warning attached to Definition 4.4a: a
quasi-stationary eigenmeasure may live on one persistent component of a regime
even though another state in the same regime exits immediately.  Hence the QSD
equation alone does not establish the statewise finite-persistence gate.
-/

namespace QSDCounterexample

noncomputable section

abbrev X := Fin 3

def actionUnit : Kernel (JointState Unit X) Unit :=
  Kernel.deterministic (fun _ => ()) (by exact Measurable.of_discrete)

def updateUnit : Kernel (UpdateInput Unit X Unit) Unit :=
  Kernel.deterministic (fun _ => ()) (by exact Measurable.of_discrete)

/-- World state 0 is absorbing, state 1 exits the regime to state 2, and state
2 remains outside. -/
def world : Kernel (WorldInput Unit X Unit) X :=
  Kernel.deterministic
    (fun z => if z.1.2 = (1 : X) then (2 : X) else z.1.2)
    (by exact Measurable.of_discrete)

def generator : StrategicGenerator Unit X Unit where
  action := actionUnit
  update := updateUnit
  action_isMarkov := by
    unfold actionUnit
    infer_instance
  update_isMarkov := by
    unfold updateUnit
    infer_instance

def model : StrategicWorldModel Unit X Unit where
  generator := generator
  world := world
  world_isMarkov := by
    unfold world
    infer_instance

def spec : RegimeSpecification (JointState Unit X) Unit where
  region := {y | y.2 ≠ (2 : X)}
  region_measurable := MeasurableSet.of_discrete
  basin := {y | y.2 = (0 : X)}
  basin_measurable := MeasurableSet.of_discrete
  basin_subset_region := by
    intro y hy
    simp only [Set.mem_setOf_eq] at hy ⊢
    omega
  descriptor := fun _ => ()
  descriptor_measurable := measurable_const
  target := ⟨Measure.dirac (), inferInstance⟩
  convergenceMode := ConvergenceMode.custom _ _ (fun _ _ _ => True)

def qsdLaw : ProbabilityMeasure (JointState Unit X) :=
  diracProba ((), (0 : X))

theorem zero_mem_region : ((), (0 : X)) ∈ spec.region := by
  simp [spec]

theorem one_mem_region : ((), (1 : X)) ∈ spec.region := by
  simp [spec]

theorem zero_transition :
    model.inducedKernel ((), (0 : X)) = Measure.dirac ((), (0 : X)) := by
  ext E hE
  rw [StrategicWorldModel.inducedKernel_apply model ((), (0 : X)) hE]
  simp [model, generator, actionUnit, updateUnit, world,
    Kernel.deterministic_apply]
  by_cases hmem : ((), (0 : X)) ∈ E <;> simp [hmem]

theorem one_exits :
    model.inducedKernel ((), (1 : X)) spec.region = 0 := by
  rw [StrategicWorldModel.inducedKernel_apply
    model ((), (1 : X)) spec.region_measurable]
  simp [model, generator, actionUnit, updateUnit, world, spec,
    Kernel.deterministic_apply]

theorem qsdLaw_supported :
    qsdLaw.toMeasure spec.region = 1 := by
  simp [qsdLaw, spec, diracProba]

theorem qsdLaw_eigen :
    killedKernel model spec ∘ₘ qsdLaw.toMeasure =
      (1 : ℝ≥0∞) • qsdLaw.toMeasure := by
  ext E hE
  rw [Measure.bind_apply hE (Kernel.aemeasurable _)]
  simp only [qsdLaw, diracProba, lintegral_dirac]
  rw [killedKernel_apply model spec ((), (0 : X)) hE, zero_transition]
  simp [zero_mem_region, hE, Measure.smul_apply]

theorem qsd_exists :
    IsQuasiStationaryDistribution model spec qsdLaw 1 := by
  refine ⟨qsdLaw_supported, zero_lt_one, le_rfl, ?_⟩
  exact qsdLaw_eigen

theorem not_uniformly_finitePersistent :
    ¬ IsFinitePersistent model spec 1 0 := by
  intro h
  have hret := h.2 ((), (1 : X)) one_mem_region
  rw [survivalProbability_eq_killedSurvivalMass
      model spec 1 one_mem_region,
    killedSurvivalMass_one, one_exits] at hret
  norm_num at hret

/-- The QSD eigenmeasure equation by itself does not imply the paper's
uniform statewise finite-persistence gate. -/
theorem qsd_does_not_imply_uniform_finitePersistence :
    IsQuasiStationaryDistribution model spec qsdLaw 1 ∧
      ¬ IsFinitePersistent model spec 1 0 :=
  ⟨qsd_exists, not_uniformly_finitePersistent⟩

end

end QSDCounterexample

end PermanssonLean
