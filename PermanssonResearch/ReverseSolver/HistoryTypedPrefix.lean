import PermanssonResearch.ReverseSolver.HistoryTypedKernel
import PermanssonLean.Probability.FinitePrefixTV
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Tactic

/-!
# D1-D2: actual typed history-dependent partialTraj law

At every elapsed time the transition depends on the whole already observed
typed joint-state history. All prefix restrictions keep the original D.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace HistoryDependentTyped

open HistoryDependent ControlledKernel FiniteStrategicRealization
open FiniteStrategicPathBridge PermanssonLean PermanssonLean.ProbabilitySupport

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov
universe uC

/-- The actual canonical history-conditioned typed finite-prefix law. -/
noncomputable def typedPrefixLaw
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D : ℕ) (x : Fin n) (t : ℕ) :
    Measure (TypedHistory n t) :=
  Kernel.partialTraj (X := fun _ : ℕ => JointState Unit (Fin n))
    (fun i => typedHistoryStep sys σ D i) 0 t
    (singletonPrefix (decode x))

instance typedPrefixLaw_isProbability
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D : ℕ) (x : Fin n) (t : ℕ) :
    IsProbabilityMeasure (typedPrefixLaw sys σ D x t) := by
  unfold typedPrefixLaw
  infer_instance

/-- No phantom first step, including at original deadline zero. -/
@[simp] theorem typedPrefixLaw_zero
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D : ℕ) (x : Fin n) :
    typedPrefixLaw sys σ D x 0 =
      Measure.dirac (singletonPrefix (decode x)) := by
  unfold typedPrefixLaw
  rw [Kernel.partialTraj_self, Kernel.id_apply]

/-- Projectivity is with the ORIGINAL deadline held fixed. -/
theorem typedPrefixLaw_projective
    {C : Type uC} [DecidableEq C] {n : ℕ}
    (sys : FiniteControlSystem C n) (σ : HistoryPolicy sys)
    (D : ℕ) (x : Fin n) {s t : ℕ} (hst : s ≤ t) :
    (typedPrefixLaw sys σ D x t).map
      (Preorder.frestrictLe₂
        (π := fun _ : ℕ => JointState Unit (Fin n)) hst) =
      typedPrefixLaw sys σ D x s := by
  unfold typedPrefixLaw
  exact Kernel.partialTraj_map_frestrictLe₂_apply
    (X := fun _ : ℕ => JointState Unit (Fin n))
    (κ := fun i => typedHistoryStep sys σ D i)
    (x₀ := singletonPrefix (decode x)) hst

end HistoryDependentTyped
end ReverseSolver
end PermanssonResearch
