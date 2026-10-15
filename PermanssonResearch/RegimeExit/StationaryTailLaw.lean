import PermanssonResearch.RegimeExit.CanonicalTailKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Tactic

/-!
# C-Exit C — genuine absolute-time continuation from a finite history

This module constructs the ORIGINAL Ionescu--Tulcea infinite-history
continuation kernel and proves projective prefix preservation and
the compositional continuation law. It is genuinely infinite-path
measure theory; the shift-to-current-state stationarity theorem is
a separate obligation and is not silently assumed below.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- The real absolute-time future continuation conditional on the
ENTIRE observed prefix through time m. Its values are probability
measures on infinite trajectories, not finite cylinder approximations. -/
noncomputable def canonicalHistoryContinuation
    (N : StrategicWorldModel S X A)
    (m : ℕ) :
    Kernel ((i : Finset.Iic m) → JointState S X)
      (ℕ → JointState S X) := by
  letI : IsMarkovKernel N.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov N
  exact Kernel.traj
    (fun n => StrategicWorldModel.stationaryHistoryKernel
      N.inducedKernel n) m

/-- Conditioning on a finite history yields a full probability law,
not a subprobability or a would-be law from an unnormalized exit mass. -/
instance canonicalHistoryContinuation_isMarkov
    (N : StrategicWorldModel S X A) (m : ℕ) :
    IsMarkovKernel (canonicalHistoryContinuation N m) := by
  unfold canonicalHistoryContinuation
  infer_instance

/-- The full continuation kernel reproduces the supplied complete
prefix with probability one. This must not be confused with a
shifted future path, whose zeroth observation is the endpoint. -/
theorem canonicalHistoryContinuation_prefix
    (N : StrategicWorldModel S X A) (m : ℕ)
    (h : (i : Finset.Iic m) → JointState S X) :
    (canonicalHistoryContinuation N m h).map
       (Preorder.frestrictLe m) =
       Measure.dirac h := by
  letI : IsMarkovKernel N.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov N
  change (Kernel.traj
      (fun n => StrategicWorldModel.stationaryHistoryKernel
        N.inducedKernel n) m h).map (Preorder.frestrictLe m) =
        Measure.dirac h
  rw [Kernel.traj_map_frestrictLe_apply]
  simp

/-- The actual complete future trajectory law composes across any
one additional stationary transition. The whole infinite trajectory
is on both sides: this is not merely equality at time m+1. -/
theorem canonicalHistoryContinuation_succ
    (N : StrategicWorldModel S X A) (m : ℕ) :
    (canonicalHistoryContinuation N (m+1)) ∘ₖ
      (Kernel.partialTraj
        (fun n => StrategicWorldModel.stationaryHistoryKernel
          N.inducedKernel n) m (m+1)) =
        canonicalHistoryContinuation N m := by
  letI : IsMarkovKernel N.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov N
  change (Kernel.traj
    (fun n => StrategicWorldModel.stationaryHistoryKernel
      N.inducedKernel n) (m+1)) ∘ₖ
    (Kernel.partialTraj
      (fun n => StrategicWorldModel.stationaryHistoryKernel
        N.inducedKernel n) m (m+1)) =
    Kernel.traj
      (fun n => StrategicWorldModel.stationaryHistoryKernel
        N.inducedKernel n) m
  exact Kernel.traj_comp_partialTraj (Nat.le_succ m)

/-- More generally, continuing an actual homogeneous trajectory
first to a later prefix and then indefinitely equals continuing
indefinitely from the earlier history. -/
theorem canonicalHistoryContinuation_comp
    (N : StrategicWorldModel S X A)
    {a b : ℕ} (hab : a ≤ b) :
    (canonicalHistoryContinuation N b) ∘ₖ
      (Kernel.partialTraj
        (fun n => StrategicWorldModel.stationaryHistoryKernel
          N.inducedKernel n) a b) =
       canonicalHistoryContinuation N a := by
  letI : IsMarkovKernel N.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov N
  change (Kernel.traj
    (fun n => StrategicWorldModel.stationaryHistoryKernel
      N.inducedKernel n) b) ∘ₖ
    (Kernel.partialTraj
      (fun n => StrategicWorldModel.stationaryHistoryKernel
        N.inducedKernel n) a b) =
    Kernel.traj
      (fun n => StrategicWorldModel.stationaryHistoryKernel
        N.inducedKernel n) a
  exact Kernel.traj_comp_partialTraj hab

end PermanssonResearch.RegimeExit
