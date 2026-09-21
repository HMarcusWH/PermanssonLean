import PermanssonLean.Intervention.Target
import PermanssonLean.StrategicWorld.Model

open ProbabilityTheory

namespace PermanssonLean

universe uS uX uA

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- A replacement Markov kernel bundled with the proof that it remains stochastic. -/
structure MarkovKernelReplacement
    (α : Type*) (β : Type*)
    [MeasurableSpace α] [MeasurableSpace β] where
  kernel : Kernel α β
  isMarkov : IsMarkovKernel kernel

/-- Replacement payload indexed by the declared intervention target.

The dependent return type prevents, for example, a world-transition replacement
from being supplied where an action-selection replacement was declared.
-/
def InterventionReplacement
    (S : Type uS) (X : Type uX) (A : Type uA)
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A] :
    InterventionTarget → Type (max (max uS uX) uA)
  | .actionSelection =>
      MarkovKernelReplacement (JointState S X) A
  | .strategicUpdate =>
      MarkovKernelReplacement (UpdateInput S X A) S
  | .worldTransition =>
      MarkovKernelReplacement (WorldInput S X A) X
  | .jointStrategic =>
      StrategicGenerator S X A

end PermanssonLean
