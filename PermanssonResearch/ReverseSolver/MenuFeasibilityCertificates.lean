import PermanssonResearch.ReverseSolver.MenuConstitutionClassification
import Mathlib.Tactic

/-!
# C9-03 — complete certificates over the DECLARED finite intervention menu

A negative result covers ALL indices of exactly the listed frozen menu,
but says nothing about admissible strategic interventions omitted from it.
No unprovided proof of baseline GR is treated as negative GR evidence.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace ReverseSolver
namespace MenuFeasibilityCertificates

set_option autoImplicit false

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.MultipleLimit.FrozenObservedEvent
open FrozenConstitutiveMenu
open MenuConstitutionClassification

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

theorem eligible_nonempty_iff_exists_listed_support
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I) :
    (supportEligibleIndices M spec F B₁ menu).Nonempty ↔
      ∃ i ∈ menu.indices, menuSupportEligible M spec F B₁ menu i := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (supportEligibleIndices_mem_iff M spec F B₁ menu i).mp hi⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i, (supportEligibleIndices_mem_iff M spec F B₁ menu i).mpr
      ⟨hi, he⟩⟩

/-- C9-B: the ORIGINAL unmodified relative PR has a witness IN THE
LISTED MENU exactly when original Exact GR holds and some listed
candidate reaches an intervened-kernel opposing recurrent class
from ALL frozen B₁ states. -/
theorem menu_exists_uniformPR_iff_exactGR_and_eligible_nonempty
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool) :
    (∃ i ∈ menu.indices,
      IsUniformGeneralizedPermanssonRegimeRelative M spec m F
        (eventuallyObservedProperty spec.descriptor true)
        B₁ (menu.choice i)) ↔
    IsExactGeneratedRegime M spec m ∧
      (supportEligibleIndices M spec F B₁ menu).Nonempty := by
  constructor
  · rintro ⟨i, hi, hpr⟩
    obtain ⟨hGR, he⟩ :=
      (listed_uniformPR_iff_exactGR_and_support
        M spec m F B₁ menu hmode i).mp hpr
    exact ⟨hGR, ⟨i,
      (supportEligibleIndices_mem_iff M spec F B₁ menu i).mpr
        ⟨hi, he⟩⟩⟩
  · rintro ⟨hGR, i, hi⟩
    obtain ⟨hmem, he⟩ :=
      (supportEligibleIndices_mem_iff M spec F B₁ menu i).mp hi
    exact ⟨i, hmem,
      (listed_uniformPR_iff_exactGR_and_support
        M spec m F B₁ menu hmode i).mpr ⟨hGR, he⟩⟩

/-- A certified eligible member is an original typed PR witness.
The baseline Exact GR certificate is supplied, not inferred from graph edges. -/
theorem eligible_index_certifies_original_relativePR
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
    (i : I) (hi : i ∈ supportEligibleIndices M spec F B₁ menu) :
    IsUniformGeneralizedPermanssonRegimeRelative M spec m F
      (eventuallyObservedProperty spec.descriptor true)
      B₁ (menu.choice i) := by
  exact (listed_uniformPR_iff_exactGR_and_support
    M spec m F B₁ menu hmode i).mpr ⟨hGR,
      (supportEligibleIndices_mem_iff M spec F B₁ menu i).mp hi |>.2⟩

/-- Only positive menu evidence promotes ONE WAY to the original
family-level uniform PR predicate; negative listed-menu evidence
does not refute a possible unlisted intervention. -/
theorem eligible_index_implies_familyPR
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
    (i : I) (hi : i ∈ supportEligibleIndices M spec F B₁ menu) :
    IsUniformGeneralizedPermanssonRegime M spec m F
      (eventuallyObservedProperty spec.descriptor true) B₁ := by
  have hPR := eligible_index_certifies_original_relativePR
    M spec m F B₁ menu hGR hmode i hi
  exact ⟨hGR, ⟨menu.choice i, hPR.2⟩⟩

/-- No eligible listed member iff ALL original listed margins are zero,
under baseline Exact GR and the literal mode. -/
theorem empty_eligible_iff_all_listed_margin_zero_of_exactGR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I)
    (hGR : IsExactGeneratedRegime M spec m)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool) :
    supportEligibleIndices M spec F B₁ menu = ∅ ↔
      ∀ i ∈ menu.indices,
        menuConstitutiveMargin M spec F B₁ menu i = 0 := by
  constructor
  · intro hem i hi
    apply support_ineligible_margin_zero M spec m F B₁
      menu hGR hmode i
    intro he
    have hmem : i ∈ supportEligibleIndices M spec F B₁ menu :=
      (supportEligibleIndices_mem_iff M spec F B₁ menu i).mpr
        ⟨hi, he⟩
    simpa [hem] using hmem
  · intro hzero
    apply Finset.ext
    intro i
    constructor
    · intro him
      obtain ⟨hi, he⟩ :=
        (supportEligibleIndices_mem_iff M spec F B₁ menu i).mp him
      have hz := hzero i hi
      exact (((margin_eq_zero_iff_not_support_of_exactGR
        M spec m F B₁ menu hGR hmode i).mp hz) he).elim
    · intro hnone
      simpa using hnone

/-- Exhaustively no original relative PR among the supplied indices
iff the listed support screen is empty, WITH baseline Exact GR. -/
theorem empty_eligible_iff_no_listed_PR_of_exactGR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I)
    (hGR : IsExactGeneratedRegime M spec m)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool) :
    supportEligibleIndices M spec F B₁ menu = ∅ ↔
      ∀ i ∈ menu.indices,
        ¬ IsUniformGeneralizedPermanssonRegimeRelative M spec m F
          (eventuallyObservedProperty spec.descriptor true)
          B₁ (menu.choice i) := by
  constructor
  · intro hem i hi hPR
    have he := ((listed_uniformPR_iff_exactGR_and_support
      M spec m F B₁ menu hmode i).mp hPR).2
    have him : i ∈ supportEligibleIndices M spec F B₁ menu :=
      (supportEligibleIndices_mem_iff M spec F B₁ menu i).mpr
        ⟨hi, he⟩
    simpa [hem] using him
  · intro hall
    apply Finset.ext
    intro i
    constructor
    · intro him
      obtain ⟨hi, he⟩ :=
        (supportEligibleIndices_mem_iff M spec F B₁ menu i).mp him
      exact (hall i hi
        ((listed_uniformPR_iff_exactGR_and_support
          M spec m F B₁ menu hmode i).mpr ⟨hGR, he⟩)).elim
    · intro hnone
      simpa using hnone

/-- Explicit menu-exhaustive negative certificate. No statement about
any other (possibly unlisted) admissible intervention or the entire F. -/
theorem finite_menu_negative_scope
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
    (hzero : supportEligibleIndices M spec F B₁ menu = ∅) :
    ∀ i ∈ menu.indices,
      menuConstitutiveMargin M spec F B₁ menu i = 0 ∧
      ¬ IsUniformGeneralizedPermanssonRegimeRelative M spec m F
        (eventuallyObservedProperty spec.descriptor true)
        B₁ (menu.choice i) := by
  intro i hi
  exact ⟨
    (empty_eligible_iff_all_listed_margin_zero_of_exactGR
      M spec m F B₁ menu hGR hmode).mp hzero i hi,
    (empty_eligible_iff_no_listed_PR_of_exactGR
      M spec m F B₁ menu hGR hmode).mp hzero i hi⟩

end MenuFeasibilityCertificates
end ReverseSolver
end PermanssonResearch
