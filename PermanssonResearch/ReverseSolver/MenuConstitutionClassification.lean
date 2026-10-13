import PermanssonResearch.ReverseSolver.FrozenConstitutiveMenu
import PermanssonResearch.MultipleLimit.FiniteObservedUniformMargin
import Mathlib.Tactic

/-!
# C9-02 — original PR and margin iff support-graph eligibility

No new PR predicate is introduced. The exact existing C8 G6 theorem
is applied separately to the actual genuine typed menu.choice i.
A baseline Exact-GR proof is needed for the POSITIVE-MARGIN iff,
but is not added to the hypotheses of the PR iff theorem itself.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace ReverseSolver
namespace MenuConstitutionClassification

set_option autoImplicit false

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.MultipleLimit.OppositeClassConstitutiveMargin
open PermanssonResearch.MultipleLimit.FiniteObservedUniformMargin
open PermanssonResearch.MultipleLimit.FrozenObservedEvent
open FrozenConstitutiveMenu

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

/-- C9-A: the original relative PR predicate for one listed member
is equivalent to C8's original baseline Exact GR plus support criterion.
Only literal mode equality is required as a separate hypothesis. -/
theorem listed_uniformPR_iff_exactGR_and_support
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool)
    (i : I) :
    IsUniformGeneralizedPermanssonRegimeRelative M spec m F
      (eventuallyObservedProperty spec.descriptor true)
      B₁ (menu.choice i) ↔
    IsExactGeneratedRegime M spec m ∧
      menuSupportEligible M spec F B₁ menu i :=
  original_uniformRelativePR_iff_opposingReachability
    M spec m F B₁ (menu.choice i) hmode

/-- Conditional on a TRUE original Exact-GR proof, a strict positive
actual original constitutive margin iff member-specific support. -/
theorem margin_pos_iff_support_of_exactGR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I)
    (hGR : IsExactGeneratedRegime M spec m)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool)
    (i : I) :
    0 < menuConstitutiveMargin M spec F B₁ menu i ↔
      menuSupportEligible M spec F B₁ menu i := by
  constructor
  · intro hp
    have huniform : IsUniformlyStrategicallyConstitutive M spec F
        (eventuallyObservedProperty spec.descriptor true)
        B₁ (menu.choice i) :=
      (uniformlyConstitutive_iff_margin_pos M spec F
        (eventuallyObservedProperty spec.descriptor true)
        B₁ (menu.choice i)).mpr hp
    exact ((listed_uniformPR_iff_exactGR_and_support
      M spec m F B₁ menu hmode i).mp ⟨hGR, huniform⟩).2
  · intro he
    have hpr := (listed_uniformPR_iff_exactGR_and_support
      M spec m F B₁ menu hmode i).mpr ⟨hGR, he⟩
    exact (uniformlyConstitutive_iff_margin_pos M spec F
      (eventuallyObservedProperty spec.descriptor true)
      B₁ (menu.choice i)).mp hpr.2

/-- C9-A: a zero margin is EXACTLY absence of support eligibility,
conditional on the original Exact-GR and literal-mode certificates. -/
theorem margin_eq_zero_iff_not_support_of_exactGR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I)
    (hGR : IsExactGeneratedRegime M spec m)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool)
    (i : I) :
    menuConstitutiveMargin M spec F B₁ menu i = 0 ↔
      ¬ menuSupportEligible M spec F B₁ menu i := by
  constructor
  · intro hz hsupport
    have hp := (margin_pos_iff_support_of_exactGR
      M spec m F B₁ menu hGR hmode i).mpr hsupport
    rw [hz] at hp
    exact (lt_irrefl (0 : ℝ) hp)
  · intro hs
    have hnot : ¬ 0 < menuConstitutiveMargin M spec F B₁ menu i := by
      intro hp
      exact hs ((margin_pos_iff_support_of_exactGR
        M spec m F B₁ menu hGR hmode i).mp hp)
    exact le_antisymm (le_of_not_gt hnot)
      (menu_margin_nonneg M spec F B₁ menu i)

/-- A structurally ineligible member has zero ORIGINAL margin,
not just a zero auxiliary score. -/
theorem support_ineligible_margin_zero
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I)
    (hGR : IsExactGeneratedRegime M spec m)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool)
    (i : I)
    (hi : ¬ menuSupportEligible M spec F B₁ menu i) :
    menuConstitutiveMargin M spec F B₁ menu i = 0 :=
  (margin_eq_zero_iff_not_support_of_exactGR
    M spec m F B₁ menu hGR hmode i).mpr hi

/-- A separately PROVED absence of baseline Exact GR forbids ALL
original relative PR claims; missing a proof is not the same thing. -/
theorem no_uniformPR_of_not_exactGR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I)
    (hnotGR : ¬ IsExactGeneratedRegime M spec m)
    (i : I) :
    ¬ IsUniformGeneralizedPermanssonRegimeRelative M spec m F
      (eventuallyObservedProperty spec.descriptor true)
      B₁ (menu.choice i) :=
  fun h => hnotGR h.1

end MenuConstitutionClassification
end ReverseSolver
end PermanssonResearch
