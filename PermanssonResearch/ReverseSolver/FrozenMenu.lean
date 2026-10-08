import PermanssonResearch.ReverseSolver.Target
import PermanssonLean.Intervention.Apply

/-!
# D0: finite menu of fixed admissible strategic interventions

The menu indices are frozen data. One index selects one already typed
admissible strategic replacement and holds it fixed for the whole horizon.
The optimum is only over this finite menu, not over adaptive controllers or
all admissible interventions. No failure of sampling is called impossibility.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace PermanssonResearch
namespace ReverseSolver

universe uS uX uA uC uI
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- A nonempty frozen finite list of explicitly typed eligible strategic
interventions, indexed independently of the intervention's proof fields. -/
structure FrozenMenu
    (M : PermanssonLean.StrategicWorldModel S X A)
    {Component : Type uC}
    (F : PermanssonLean.InterventionFamily M Component)
    (I : Type uI) where
  indices : Finset I
  nonempty : indices.Nonempty
  choice : I → PermanssonLean.AdmissibleStrategicIntervention F

/-- The value of one fixed member uses its genuine induced strategic/world
kernel and the exact finite-prefix hitting event. -/
noncomputable def memberValue
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {I : Type uI}
    (menu : FrozenMenu M F I)
    (target : FrozenHittingTarget (PermanssonLean.JointState S X))
    (y : PermanssonLean.JointState S X) (T : ℕ) (i : I) : ℝ :=
  hittingValue target (menu.choice i).intervention.apply.inducedKernel y T

/-- A finite nonempty menu has a globally optimal member for the *frozen
menu*, even when two distinct indices carry identical interventions. -/
theorem exists_optimal_member
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {I : Type uI}
    (menu : FrozenMenu M F I)
    (target : FrozenHittingTarget (PermanssonLean.JointState S X))
    (y : PermanssonLean.JointState S X) (T : ℕ) :
    ∃ i ∈ menu.indices,
      ∀ j ∈ menu.indices, memberValue menu target y T j ≤
        memberValue menu target y T i := by
  classical
  exact Finset.exists_max_image menu.indices
    (memberValue menu target y T) menu.nonempty

/-- A selected exact argmax exists noncomputably. A later executable
D0 evaluator must show which finite arithmetic representation it uses. -/
noncomputable def optimalMember
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {I : Type uI}
    (menu : FrozenMenu M F I)
    (target : FrozenHittingTarget (PermanssonLean.JointState S X))
    (y : PermanssonLean.JointState S X) (T : ℕ) : I :=
  Classical.choose (exists_optimal_member menu target y T)

theorem optimalMember_mem
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {I : Type uI}
    (menu : FrozenMenu M F I)
    (target : FrozenHittingTarget (PermanssonLean.JointState S X))
    (y : PermanssonLean.JointState S X) (T : ℕ) :
    optimalMember menu target y T ∈ menu.indices :=
  (Classical.choose_spec (exists_optimal_member menu target y T)).1

theorem optimalMember_dominates
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {I : Type uI}
    (menu : FrozenMenu M F I)
    (target : FrozenHittingTarget (PermanssonLean.JointState S X))
    (y : PermanssonLean.JointState S X) (T : ℕ)
    (j : I) (hj : j ∈ menu.indices) :
    memberValue menu target y T j ≤
      memberValue menu target y T (optimalMember menu target y T) :=
  (Classical.choose_spec (exists_optimal_member menu target y T)).2 j hj

/-- The selected intervention is typed strategic, hence its transition
factorization preserves the baseline world primitive P. -/
theorem optimalMember_world_eq
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {I : Type uI}
    (menu : FrozenMenu M F I)
    (target : FrozenHittingTarget (PermanssonLean.JointState S X))
    (y : PermanssonLean.JointState S X) (T : ℕ) :
    (menu.choice (optimalMember menu target y T)).intervention.apply.world =
      M.world :=
  (menu.choice (optimalMember menu target y T)).world_eq

/-- Each frozen-menu membership is an admissible strategic intervention,
never a structural world-P edit. -/
theorem memberValue_nonneg
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {I : Type uI}
    (menu : FrozenMenu M F I)
    (target : FrozenHittingTarget (PermanssonLean.JointState S X))
    (y : PermanssonLean.JointState S X) (T : ℕ) (i : I) :
    0 ≤ memberValue menu target y T i :=
  hittingValue_nonneg target (menu.choice i).intervention.apply.inducedKernel y T


/-- If the chosen optimal success probability is zero, every *eligible*
member has probability zero. No claim about interventions outside menu. -/
theorem all_menu_values_zero_of_optimal_zero
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {I : Type uI}
    (menu : FrozenMenu M F I)
    (target : FrozenHittingTarget (PermanssonLean.JointState S X))
    (y : PermanssonLean.JointState S X) (T : ℕ)
    (hzero : memberValue menu target y T
      (optimalMember menu target y T) = 0) :
    ∀ j ∈ menu.indices, memberValue menu target y T j = 0 := by
  intro j hj
  apply le_antisymm
  · calc
      memberValue menu target y T j ≤
          memberValue menu target y T (optimalMember menu target y T) :=
        optimalMember_dominates menu target y T j hj
      _ = 0 := hzero
  · exact memberValue_nonneg menu target y T j

end ReverseSolver
end PermanssonResearch
