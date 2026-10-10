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

end TypedStrategicWitness
end MultipleLimit
end PermanssonResearch
