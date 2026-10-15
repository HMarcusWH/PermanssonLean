import PermanssonResearch.RegimeExit.StationaryTailLaw
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# C-Exit C — whole-path continuation conditional on a finite prefix

This is a FULL infinite-path measure identity, at a deterministic
time: the prefix/full-trajectory joint law equals the canonical
prefix marginal composed with the Ionescu--Tulcea continuation
kernel from the full observed history.

This is not yet a theorem that the shifted future depends only on
the LAST state. Proving that homogeneous stationarity reduction,
then applying the first-exit cylinder, are separate obligations.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- The actual point-started infinite-path law and its prefix have
the exact joint distribution of prefix then original Ionescu--Tulcea
continuation. This equality is not restricted to finite cylinders. -/
theorem pointPathLaw_history_joint
    (N : StrategicWorldModel S X A)
    (z : JointState S X)
    (m : ℕ) :
    (N.pathLaw (Measure.dirac z)).map
      (fun w : ℕ → JointState S X =>
        (Preorder.frestrictLe m w, w)) =
    ((N.pathLaw (Measure.dirac z)).map
        (Preorder.frestrictLe m)) ⊗ₘ
          (canonicalHistoryContinuation N m) := by
  letI : IsMarkovKernel N.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov N
  let κ : (n : ℕ) →
      Kernel ((i : Finset.Iic n) → JointState S X)
        (JointState S X) :=
    fun n => StrategicWorldModel.stationaryHistoryKernel N.inducedKernel n
  let u : (i : Finset.Iic (0 : ℕ)) → JointState S X :=
    fun _ => z
  have hz :
      N.pathLaw (Measure.dirac z) = Kernel.traj κ 0 u := by
    rw [←canonicalFutureKernel_apply N z]
    rfl
  rw [hz]
  change (Kernel.traj κ 0 u).map
    (fun w => (Preorder.frestrictLe m w, w)) =
    ((Kernel.traj κ 0 u).map (Preorder.frestrictLe m)) ⊗ₘ
      (Kernel.traj κ m)
  rw [Kernel.traj_map_frestrictLe_apply]
  exact (Kernel.partialTraj_compProd_traj (κ := κ)
    (a := 0) (b := m) (Nat.zero_le m) u).symm

end PermanssonResearch.RegimeExit
