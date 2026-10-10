import PermanssonResearch.MultipleLimit.ExactRationalAbsorption
import PermanssonResearch.MultipleLimit.AbsorbingFamily
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Deterministic
import Mathlib.Tactic

/-!
# Lane C1 — genuinely random typed alpha/P/U witness

The four Boolean joint states are t,u,a,b. Selection of action at u
determines a 1/2 self-loop versus branching. On the branch action, world
P supplies a second Bernoulli draw (1/3 a, 2/3 b) and the strategic
update switches to the absorbing strategic state. Frozen P is the actual
world kernel, not a numerically postulated transition matrix.

The induced-kernel row equalities and canonical almost-sure absorption
bridge are separate proof obligations; merely constructing this model
does NOT certify the entire C1 package.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedStrategicWitness

open PermanssonLean

abbrev Y := JointState Bool Bool
def t : Y := (false, false)
def u : Y := (false, true)
def a : Y := (true, false)
def b : Y := (true, true)

noncomputable def half : unitInterval := ⟨(1/2 : ℝ), by norm_num⟩
noncomputable def twoThirds : unitInterval := ⟨(2/3 : ℝ), by norm_num⟩

noncomputable def selection : Kernel Y Bool :=
  Kernel.const _ (bernoulliMeasure true false half)

/-- The branch subkernel is a real random draw of the next world state. -/
noncomputable def branchWorld : Kernel (WorldInput Bool Bool Bool) Bool :=
  Kernel.const _ (bernoulliMeasure true false twoThirds)

/-- From t we enter u; outside the branch, we hold the old world value. -/
noncomputable def otherWorld : Kernel (WorldInput Bool Bool Bool) Bool :=
  Kernel.deterministic
    (fun z => if z.1 = t then true else z.1.2)
    (by exact Measurable.of_discrete)

/-- At u with action false, take the random branch instead of self-loop. -/
def branchRegion : Set (WorldInput Bool Bool Bool) :=
  {z | z.1 = u ∧ z.2 = false}

noncomputable def world : Kernel (WorldInput Bool Bool Bool) Bool := by
  classical
  exact Kernel.piecewise
    (s := branchRegion) MeasurableSet.of_discrete branchWorld otherWorld

/-- The strategic bit records whether a branch was taken. -/
def updateNext (z : UpdateInput Bool Bool Bool) : Bool :=
  if z.1.1 = t then false
  else if z.1.1 = u ∧ z.1.2 = true then false
  else true

noncomputable def update : Kernel (UpdateInput Bool Bool Bool) Bool :=
  Kernel.deterministic updateNext (by exact Measurable.of_discrete)

/-- Actual typed state/action/world/update Markov model. Its kernels are
state dependent and both action selection and world branching are random. -/
noncomputable def model : StrategicWorldModel Bool Bool Bool where
  generator := {
    action := selection
    update := update
    action_isMarkov := by unfold selection; infer_instance
    update_isMarkov := by unfold update; infer_instance }
  world := world
  world_isMarkov := by
    unfold world branchWorld otherWorld
    infer_instance


/-- Normalize the piecewise world kernel without unfolding the
proof-irrelevant measurable-set certificate in subsequent integrals. -/
theorem world_row (y : Y) (act : Bool) :
    world (y, act) =
      if y = u ∧ act = false then
        bernoulliMeasure true false twoThirds
      else Measure.dirac (if y = t then true else y.2) := by
  classical
  unfold world
  rw [Kernel.piecewise_apply]
  simp [branchRegion, branchWorld, otherWorld,
    Kernel.const_apply, Kernel.deterministic_apply]

/-- Exact Bernoulli integration against the actual finite action/world
measure, used below to expose the genuine alpha/P/U transition rows. -/
private theorem bernoulli_bool_lintegral (p : unitInterval)
    (f : Bool → ℝ≥0∞) :
    (∫⁻ z, f z ∂bernoulliMeasure true false p) =
      (unitInterval.toNNReal p) • f true +
        (unitInterval.toNNReal (unitInterval.symm p)) • f false := by
  simp [bernoulliMeasure_def, lintegral_add_measure, lintegral_smul_measure]


/-- First literal atom of the stochastic typed witness. This tests the
same induced-kernel integral used by the complete four-row theorem. -/
theorem induced_t_to_u :
    model.inducedKernel t {u} = 1 := by
  classical
  rw [StrategicWorldModel.inducedKernel_apply model t
    (measurableSet_singleton u)]
  simp [model, selection, update, updateNext, world_row,
    branchRegion, t, u, Kernel.const_apply,
    Kernel.deterministic_apply, Kernel.piecewise_apply,
    bernoulli_bool_lintegral, half, twoThirds, Measure.dirac_apply]


/-- The transient branching state reaches the first absorbing state with
exactly 1/6 one-step probability, not an assumed rational row. -/
theorem induced_u_to_a :
    model.inducedKernel u {a} = (1/6 : ℝ≥0∞) := by
  classical
  rw [StrategicWorldModel.inducedKernel_apply model u
    (measurableSet_singleton a)]
  simp [model, selection, update, updateNext, world_row,
    branchRegion, t, u, a, Kernel.const_apply,
    Kernel.deterministic_apply, Kernel.piecewise_apply,
    bernoulli_bool_lintegral, Measure.dirac_apply]
  rw [ENNReal.smul_def, smul_eq_mul, ← ENNReal.coe_mul]
  norm_num [half, twoThirds, unitInterval.toNNReal,
    unitInterval.symm, Pi.single_apply]


/-- Enumeration of the physical Boolean strategic-world states in the
same frozen order as the independently certified rational reference. -/
def codeState : Y → Fin 4
  | (false, false) => 0
  | (false, true) => 1
  | (true, false) => 2
  | (true, true) => 3

/-- Every *actual* alpha/P/U one-step atom agrees with its exact rational
entry, with no assumed matrix correspondence. -/
theorem inducedKernel_atom_entry (y z : Y) :
    model.inducedKernel y {z} =
      ENNReal.ofReal
        ((ExactRationalAbsorption.fourStateMatrix.entry (codeState y) (codeState z) : ℚ) : ℝ) := by
  classical
  rcases y with ⟨ys, yx⟩
  rcases z with ⟨zs, zx⟩
  cases ys <;> cases yx <;> cases zs <;> cases zx
  all_goals
    rw [StrategicWorldModel.inducedKernel_apply model _
      (measurableSet_singleton _)]
    simp [model, selection, update, updateNext, world_row,
      t, u, a, b, codeState, ExactRationalAbsorption.fourStateMatrix,
      Kernel.const_apply, Kernel.deterministic_apply,
      bernoulli_bool_lintegral, Measure.dirac_apply,
      ENNReal.smul_def, smul_eq_mul]
    <;> norm_num [half, twoThirds, unitInterval.toNNReal,
      unitInterval.symm, ENNReal.smul_def, smul_eq_mul]

end TypedStrategicWitness
end MultipleLimit
end PermanssonResearch
