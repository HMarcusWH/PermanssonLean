import Mathlib.Probability.Kernel.Basic

open MeasureTheory
open ProbabilityTheory

namespace PermanssonLean

universe uS uX uA

/-- Joint strategic-world state. -/
abbrev JointState (S : Type uS) (X : Type uX) := S × X

/-- Input seen by the world-transition kernel after action selection. -/
abbrev WorldInput (S : Type uS) (X : Type uX) (A : Type uA) :=
  (JointState S X) × A

/-- Input seen by the strategic-update kernel after the next world state is realized. -/
abbrev UpdateInput (S : Type uS) (X : Type uX) (A : Type uA) :=
  (WorldInput S X A) × X

/--
The strategic generator from Permansson v0.1.7.

* `action` formalizes the action-selection kernel α(da | s,x).
* `update` formalizes the strategic-update kernel U(ds' | s,x,a,x').
-/
structure StrategicGenerator
    (S : Type uS) (X : Type uX) (A : Type uA)
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A] where
  action : Kernel (JointState S X) A
  update : Kernel (UpdateInput S X A) S
  action_isMarkov : IsMarkovKernel action
  update_isMarkov : IsMarkovKernel update

/--
Canonical typed strategic-world model.

The world kernel has paper type P(dx' | s,x,a).
No induced joint kernel is defined here yet; that construction is the first proof milestone.
-/
structure StrategicWorldModel
    (S : Type uS) (X : Type uX) (A : Type uA)
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A] where
  generator : StrategicGenerator S X A
  world : Kernel (WorldInput S X A) X
  world_isMarkov : IsMarkovKernel world

end PermanssonLean
