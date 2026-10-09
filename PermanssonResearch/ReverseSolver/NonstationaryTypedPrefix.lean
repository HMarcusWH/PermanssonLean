import PermanssonResearch.ReverseSolver.NonstationaryTypedKernel
import PermanssonLean.Probability.FinitePrefixTV
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Tactic

/-!
# D1-C2: actual typed time-inhomogeneous prefix measure

The time-indexed history kernels are obtained by canonical composition
of alpha -> P -> U at each remaining-horizon step. The trajectory is a
genuine Mathlib partialTraj law, not a stationary finitePrefixLaw of one
fixed intervention. All restrictions preserve the ORIGINAL deadline D.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace NonstationaryTyped

open Bellman
open ControlledKernel
open FiniteStrategicRealization
open FiniteStrategicPathBridge
open PermanssonLean
open PermanssonLean.ProbabilitySupport

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov
universe uC

/-- Typed extension kernel: inspect last JOINT strategic-world state,
and apply the actual time-selected induced alpha/P/U kernel. -/
noncomputable def typedHistoryStep {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D i : ℕ) :
    Kernel ((j : Finset.Iic i) → JointState Unit (Fin n))
      (JointState Unit (Fin n)) :=
  (selectedTypedKernel sys pi D i).comap
    (fun w => w ⟨i, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance typedHistoryStep_isMarkov
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D i : ℕ) : IsMarkovKernel (typedHistoryStep sys pi D i) := by
  unfold typedHistoryStep
  infer_instance

/-- The actual typed time-inhomogeneous partialTraj distribution
through t transitions, keeping the initial deadline D fixed. -/
noncomputable def typedPrefixLaw {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D : ℕ) (x : Fin n) (t : ℕ) :
    Measure ((j : Finset.Iic t) → JointState Unit (Fin n)) :=
  Kernel.partialTraj
    (X := fun _ : ℕ => JointState Unit (Fin n))
    (fun i => typedHistoryStep sys pi D i) 0 t
    (singletonPrefix (decode x))

instance typedPrefixLaw_isProbability
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D : ℕ) (x : Fin n) (t : ℕ) :
    IsProbabilityMeasure (typedPrefixLaw sys pi D x t) := by
  unfold typedPrefixLaw
  infer_instance

/-- The initial distribution is exactly a one-point mass at the decoded
strategic-world initial state, including at deadline zero. -/
theorem typedPrefixLaw_zero {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D : ℕ) (x : Fin n) :
    typedPrefixLaw sys pi D x 0 =
      Measure.dirac (singletonPrefix (decode x)) := by
  unfold typedPrefixLaw
  rw [Kernel.partialTraj_self, Kernel.id_apply]

/-- A single deadline-conditioned process is projective in its prefix
length. Cross-DEADLINE projectivity is neither assumed nor claimed. -/
theorem typedPrefixLaw_projective
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (pi : MarkovSchedule sys)
    (D : ℕ) (x : Fin n) {s t : ℕ} (hst : s ≤ t) :
    (typedPrefixLaw sys pi D x t).map
      (Preorder.frestrictLe₂
        (π := fun _ : ℕ => JointState Unit (Fin n)) hst) =
    typedPrefixLaw sys pi D x s := by
  unfold typedPrefixLaw
  exact Kernel.partialTraj_map_frestrictLe₂_apply
    (X := fun _ : ℕ => JointState Unit (Fin n))
    (κ := fun i => typedHistoryStep sys pi D i)
    (x₀ := singletonPrefix (decode x)) hst

/-- If the state-feedback rule is stationary, the typed nonstationary
construction reduces to the existing canonical finitePrefixLaw of the
induced feedback model. This is a theorem about genuinely equal laws. -/
theorem typedPrefixLaw_stationary {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (rho : StateFeedback sys)
    (D t : ℕ) (x : Fin n) :
    typedPrefixLaw sys (stationarySchedule rho) D x t =
      finitePrefixLaw (feedbackModel sys rho).inducedKernel (decode x) t := by
  rfl

end NonstationaryTyped
end ReverseSolver
end PermanssonResearch
