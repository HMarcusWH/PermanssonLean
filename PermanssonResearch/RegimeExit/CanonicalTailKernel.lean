import PermanssonResearch.RegimeExit.SwitchRestart
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Tactic

/-!
# Lane C-Exit C — actual canonical infinite-future Markov kernel

The future-path kernel is obtained directly from the original stationary
\`α → P → U\` induced Markov kernel. In particular its values are genuine
probability measures on *infinite paths*, not pointwise distributions or
unnormalized first-exit submeasures.

This file does not assume a stopped-process restart identity.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- The post-time-m infinite tail re-indexed at zero. It is a
time-shift, not a truncated prefix, and m is always finite. -/
def pathTailShift (m : ℕ)
    (w : ℕ → JointState S X) : ℕ → JointState S X :=
  fun t => w (m + t)

/-- Time shifting is measurable in the canonical countable product
measurable space; no discreteness or finite state assumption. -/
theorem measurable_pathTailShift (m : ℕ) :
    Measurable (pathTailShift (S := S) (X := X) (A := A) m) := by
  apply measurable_pi_iff.mpr
  intro t
  exact measurable_pi_apply (m + t)

/-- The true canonical infinite-future kernel from the current state.
The Ionescu--Tulcea measure at the singleton time-zero prefix is Markov
and lives on the ORIGINAL infinite trajectory space. -/
noncomputable def canonicalFutureKernel
    (N : StrategicWorldModel S X A) :
    Kernel (JointState S X) (ℕ → JointState S X) := by
  letI : IsMarkovKernel N.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov N
  exact (Kernel.traj
    (fun n => StrategicWorldModel.stationaryHistoryKernel
      N.inducedKernel n) 0).comap
    (MeasurableEquiv.piUnique
      (fun _ : Finset.Iic (0 : ℕ) => JointState S X)).symm
    (MeasurableEquiv.measurable _)

/-- The future kernel is a true Markov kernel (mass exactly one at
every starting state); it is not the first-exit subkernel. -/
instance canonicalFutureKernel_isMarkov
    (N : StrategicWorldModel S X A) :
    IsMarkovKernel (canonicalFutureKernel N) := by
  unfold canonicalFutureKernel
  infer_instance

/-- The future kernel is IDENTICAL to the model's frozen canonical
path law from a Dirac initial state, without any new physical kernel. -/
theorem canonicalFutureKernel_apply
    (N : StrategicWorldModel S X A)
    (z : JointState S X) :
    canonicalFutureKernel N z = N.pathLaw (Measure.dirac z) := by
  letI : IsMarkovKernel N.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov N
  unfold canonicalFutureKernel StrategicWorldModel.pathLaw Kernel.trajMeasure
  rw [Measure.map_dirac z]
  rw [Measure.dirac_bind (Kernel.measurable _)]
  rfl

/-- A genuinely point-started infinite future has current state z at
its own time zero. This is the basic indexing check for the restart law. -/
theorem canonicalFutureKernel_zero_marginal
    (N : StrategicWorldModel S X A)
    (z : JointState S X) :
    (canonicalFutureKernel N z).map
      (fun w : ℕ → JointState S X => w 0) = Measure.dirac z := by
  rw [canonicalFutureKernel_apply]
  exact StrategicWorldModel.pathLaw_eval_zero N (Measure.dirac z)

end PermanssonResearch.RegimeExit
