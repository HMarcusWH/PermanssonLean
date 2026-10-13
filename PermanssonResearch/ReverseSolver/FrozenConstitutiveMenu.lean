import PermanssonResearch.ReverseSolver.FrozenMenu
import PermanssonResearch.MultipleLimit.OppositeClassConstitutiveMargin
import PermanssonLean.Regime.UniformPermansson
import Mathlib.Tactic

/-!
# C9-01 — the original finite menu with a separate structural eligibility screen

An index denotes exactly the already typed member of D0's FrozenMenu.
The Boolean support screen is computed from THAT MEMBER'S intervened
induced kernel; it is NOT the original regime predicate and does not
substitute for a numerical constitutive margin.

The menu indices and ex ante comparison set are fixed and nonempty.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace ReverseSolver
namespace FrozenConstitutiveMenu

set_option autoImplicit false

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.MultipleLimit.OppositeClassConstitutiveMargin
open PermanssonResearch.MultipleLimit.FrozenObservedEvent

variable {S X A I : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [TopologicalSpace S] [TopologicalSpace X]
variable [Fintype (JointState S X)] [Nonempty (JointState S X)]
variable [DecidableEq (JointState S X)]
variable [MeasurableSingletonClass (JointState S X)]
variable [DiscreteTopology (JointState S X)]
variable [OpensMeasurableSpace (JointState S X)]
variable [StandardBorelSpace (JointState S X)]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- The exact graph criterion of C8 applied to the genuine intervened
kernel attached to member i, at EVERY frozen comparison start. -/
def menuSupportEligible
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I) (i : I) : Prop :=
  ∀ y ∈ B₁.states,
    OpposingClassReachable
      (menu.choice i).intervention.apply.inducedKernel
      spec.descriptor spec.target y

/-- Subset of exactly the supplied D0 menu, obtained by classical
finite filtering. This is not yet a verified executable graph search. -/
noncomputable def supportEligibleIndices
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I) : Finset I := by
  classical
  exact menu.indices.filter (menuSupportEligible M spec F B₁ menu)

/-- The ACTUAL original uniform constitutive margin. D0's
finite-horizon hitting value is intentionally not used here. -/
noncomputable def menuConstitutiveMargin
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I) (i : I) : ℝ :=
  constitutiveMargin M spec F
    (eventuallyObservedProperty spec.descriptor true)
    B₁ (menu.choice i)

theorem supportEligibleIndices_mem_iff
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I) (i : I) :
    i ∈ supportEligibleIndices M spec F B₁ menu ↔
      i ∈ menu.indices ∧ menuSupportEligible M spec F B₁ menu i := by
  classical
  simp only [supportEligibleIndices, Finset.mem_filter]

theorem menu_margin_nonneg
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I) (i : I) :
    0 ≤ menuConstitutiveMargin M spec F B₁ menu i :=
  constitutiveMargin_nonneg M spec F
    (eventuallyObservedProperty spec.descriptor true) B₁
    (menu.choice i)

end FrozenConstitutiveMenu
end ReverseSolver
end PermanssonResearch
