import PermanssonResearch.Perturbation.FiniteMetricProtocol

/-! Nonzero weighted-cost and zero-contraction regressions on actual typed
models. Both coordinates change, so erasing either weight fails this check. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace PermanssonResearch.Perturbation.FiniteSequential.MetricFixture
open PermanssonLean PermanssonResearch.Probability
noncomputable section

def boolMetric : MetricSpace Bool where
  dist x y := if x=y then 0 else 1
  dist_self _ := by simp
  dist_comm x y := by cases x <;> cases y <;> simp
  dist_triangle x y z := by cases x <;> cases y <;> cases z <;> norm_num
  eq_of_dist_eq_zero := by
    intro x y h
    by_cases hh : x=y
    · exact hh
    · simp [hh] at h

local instance : MetricSpace Bool := boolMetric
local instance : MeasurableSpace Bool := ⊤
local instance : DiscreteMeasurableSpace Bool := ⟨fun _ => trivial⟩

theorem bool_dist (x y : Bool) : dist x y=if x=y then 0 else 1 := rfl
attribute [local simp] bool_dist Kernel.deterministic_apply

def model (c : Bool) : StrategicWorldModel Bool Bool Bool where
  generator := {
    action := Kernel.const (JointState Bool Bool) (Measure.dirac c)
    update := Kernel.deterministic (fun w : UpdateInput Bool Bool Bool => w.1.2) (measurable_of_finite _)
    action_isMarkov := inferInstance
    update_isMarkov := inferInstance }
  world := Kernel.deterministic (fun w : WorldInput Bool Bool Bool => w.2) (measurable_of_finite _)
  world_isMarkov := inferInstance

theorem dirac_dual (x y : Bool) : W1DualLE (Measure.dirac x) (Measure.dirac y) (dist x y) := by
  intro f hf
  rw [integral_dirac' f x hf.measurable.stronglyMeasurable,
    integral_dirac' f y hf.measurable.stronglyMeasurable]
  simpa [Real.dist_eq] using hf.lipschitz.dist_le_mul x y

def errors : PrimitiveMetricBounds (model false) (model true) where
  actionError := 1
  worldError := 0
  updateError := 0
  worldAction := 1
  updateAction := 1
  updateWorld := 0
  action _ := by simpa [model,boolMetric] using dirac_dual false true
  world y c := W1DualLE.refl _
  update y c x := W1DualLE.refl _
  referenceWorldAction y c d := by simpa [model] using dirac_dual c d
  referenceUpdateAction y c d x := by simpa [model] using dirac_dual c d
  referenceUpdateWorld y c x z := by simpa [model] using W1DualLE.refl (Measure.dirac c)

theorem budget_five : errors.budget 2 3=5 := by
  norm_num [PrimitiveMetricBounds.budget,metricBudget,errors]

theorem actual_weighted_defect (y : JointState Bool Bool) :
    letI : PseudoMetricSpace (JointState Bool Bool) := weightedMetric 2 3
    W1DualLE ((model false).inducedKernel y) ((model true).inducedKernel y) 5 := by
  simpa only [budget_five] using errors.weighted_induced_bound 2 3 y

theorem model_induced (c : Bool) (y : JointState Bool Bool) :
    (model c).inducedKernel y=Measure.dirac (c,c) := by
  classical
  apply Measure.ext
  intro E hE
  rw [StrategicWorldModel.inducedKernel_apply _ _ hE]
  simp [model,Kernel.deterministic_apply,Measure.dirac_apply',hE,Set.indicator]

theorem weighted_distance_five : weightedDistance (2:ℝ≥0) 3 (false,false) (true,true)=5 := by
  norm_num [weightedDistance,bool_dist]

theorem actual_weighted_coupling_cost (y : JointState Bool Bool) :
    letI : PseudoMetricSpace (JointState Bool Bool) := weightedMetric 2 3
    ∃ γ : IntegrableCoupling ((model false).inducedKernel y) ((model true).inducedKernel y),
      γ.cost=5 := by
  letI : PseudoMetricSpace (JointState Bool Bool) := weightedMetric 2 3
  rw [model_induced,model_induced]
  let γ : IntegrableCoupling (Measure.dirac (false,false)) (Measure.dirac (true,true)) := {
    law := Measure.dirac ((false,false),(true,true))
    isProbability := inferInstance
    first := by simp
    second := by simp
    cost_integrable := Integrable.of_finite }
  refine ⟨γ,?_⟩
  change (∫ z,weightedDistance (2:ℝ≥0) 3 z.1 z.2 ∂Measure.dirac ((false,false),(true,true)))=5
  rw [integral_dirac' _ _ (measurable_of_finite _).stronglyMeasurable]
  exact weighted_distance_five

def stateBounds (c : Bool) (dold : JointState Bool Bool → JointState Bool Bool → ℝ) :
    StateMetricBounds (model c) dold where
  actionState := 0
  worldState := 0
  updateState := 0
  worldAction := 1
  updateAction := 1
  updateWorld := 0
  action y z := by simpa [model] using W1DualLE.refl (Measure.dirac c)
  world y z d := by simpa [model] using W1DualLE.refl (Measure.dirac d)
  update y z d x := by simpa [model] using W1DualLE.refl (Measure.dirac d)
  world_action y c d := by simpa [model] using dirac_dual c d
  update_action y c d x := by simpa [model] using dirac_dual c d
  update_world y c x z := by simpa [model] using W1DualLE.refl (Measure.dirac c)

theorem factor_zero (c : Bool) (dold) : (stateBounds c dold).factor 2 3=0 := by
  norm_num [StateMetricBounds.factor,metricBudget,stateBounds]

theorem original_contraction_zero (c : Bool) : IsW1Contraction (model c).inducedKernel 0 := by
  have hh := (stateBounds c (fun y z => dist y z)).original_isW1Contraction
    2 3 (by norm_num) (by norm_num)
  simpa only [factor_zero,zero_div] using hh

theorem weighted_contraction_zero (c : Bool) :
    letI : PseudoMetricSpace (JointState Bool Bool) := weightedMetric 2 3
    IsW1Contraction (model c).inducedKernel 0 := by
  simpa only [factor_zero] using (stateBounds c (weightedDistance 2 3)).weighted_isW1Contraction 2 3

theorem strict_metric_gate (c : Bool) :
    (stateBounds c (fun y z => dist y z)).factor 2 3/min (2:ℝ) 3<1 := by
  rw [factor_zero]
  norm_num

/-- A second comparison changes P between models. U copies the realized
next world, so its world Lipschitz factor must propagate the world error. -/
def worldModel (c : Bool) : StrategicWorldModel Bool Bool Bool where
  generator := {
    action := Kernel.const (JointState Bool Bool) (Measure.dirac false)
    update := Kernel.deterministic (fun w : UpdateInput Bool Bool Bool => w.2) (measurable_of_finite _)
    action_isMarkov := inferInstance
    update_isMarkov := inferInstance }
  world := Kernel.const (WorldInput Bool Bool Bool) (Measure.dirac c)
  world_isMarkov := inferInstance

def worldErrors : PrimitiveMetricBounds (worldModel false) (worldModel true) where
  actionError := 0
  worldError := 1
  updateError := 0
  worldAction := 0
  updateAction := 0
  updateWorld := 1
  action y := W1DualLE.refl _
  world y c := by simpa [worldModel,boolMetric] using dirac_dual false true
  update y c x := W1DualLE.refl _
  referenceWorldAction y c d := by simpa [worldModel] using W1DualLE.refl (Measure.dirac true)
  referenceUpdateAction y c d x := by simpa [worldModel] using W1DualLE.refl (Measure.dirac x)
  referenceUpdateWorld y c x z := by simpa [worldModel] using dirac_dual x z

theorem world_budget_five : worldErrors.budget 2 3=5 := by
  norm_num [PrimitiveMetricBounds.budget,metricBudget,worldErrors]

theorem actual_world_weighted_defect (y : JointState Bool Bool) :
    letI : PseudoMetricSpace (JointState Bool Bool) := weightedMetric 2 3
    W1DualLE ((worldModel false).inducedKernel y) ((worldModel true).inducedKernel y) 5 := by
  simpa only [world_budget_five] using worldErrors.weighted_induced_bound 2 3 y

theorem world_model_induced (c : Bool) (y : JointState Bool Bool) :
    (worldModel c).inducedKernel y=Measure.dirac (c,c) := by
  classical
  apply Measure.ext
  intro E hE
  rw [StrategicWorldModel.inducedKernel_apply _ _ hE]
  simp [worldModel,Kernel.deterministic_apply,Measure.dirac_apply',hE,Set.indicator]

theorem actual_world_weighted_cost (y : JointState Bool Bool) :
    letI : PseudoMetricSpace (JointState Bool Bool) := weightedMetric 2 3
    ∃ γ : IntegrableCoupling ((worldModel false).inducedKernel y) ((worldModel true).inducedKernel y),
      γ.cost=5 := by
  letI : PseudoMetricSpace (JointState Bool Bool) := weightedMetric 2 3
  have hh := actual_weighted_coupling_cost y
  rw [model_induced,model_induced] at hh
  rw [world_model_induced,world_model_induced]
  exact hh

end
end PermanssonResearch.Perturbation.FiniteSequential.MetricFixture
