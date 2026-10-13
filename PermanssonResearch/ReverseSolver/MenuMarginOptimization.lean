import PermanssonResearch.ReverseSolver.MenuFeasibilityCertificates
import PermanssonResearch.MultipleLimit.TypedObservedSupportInvariance
import PermanssonResearch.MultipleLimit.TypedObservedEventConstitution
import Mathlib.Tactic

/-!
# C9-04 — quantitative original-margin maximization on the frozen menu

Feasibility is a qualitative support question (C8). Optimization is
over the genuinely original real-valued constitutive margin and does
not reuse D0's finite-horizon hitting-value objective or its argmax.
All choices here may be classical/noncomputable.

The universal probability-event margin upper bound one makes C6's
previously certified full-disruption witness an exact optimizer.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace ReverseSolver
namespace MenuMarginOptimization

set_option autoImplicit false

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.MultipleLimit.FrozenObservedEvent
open PermanssonResearch.MultipleLimit.TypedObservedEventConstitution
open PermanssonResearch.MultipleLimit.TypedObservedSupportInvariance
open PermanssonResearch.MultipleLimit.ObservedSupportInvariance
open FrozenConstitutiveMenu
open MenuConstitutionClassification
open MenuFeasibilityCertificates

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

/-- A global mathematical maximum exists on EVERY finite nonempty
original menu, regardless of whether Exact GR has been established. -/
theorem exists_maximum_listed_margin
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I) :
    ∃ i ∈ menu.indices, ∀ j ∈ menu.indices,
      menuConstitutiveMargin M spec F B₁ menu j ≤
      menuConstitutiveMargin M spec F B₁ menu i := by
  classical
  exact Finset.exists_max_image menu.indices
    (menuConstitutiveMargin M spec F B₁ menu) menu.nonempty

/-- An eligible maximum is a global max against EVERY listed candidate,
not just the eligible ones: all excluded original margins equal zero. -/
theorem exists_optimal_eligible_of_nonempty
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
    (hne : (supportEligibleIndices M spec F B₁ menu).Nonempty) :
    ∃ i ∈ supportEligibleIndices M spec F B₁ menu,
      0 < menuConstitutiveMargin M spec F B₁ menu i ∧
      (∀ j ∈ menu.indices,
        menuConstitutiveMargin M spec F B₁ menu j ≤
          menuConstitutiveMargin M spec F B₁ menu i) ∧
      IsUniformGeneralizedPermanssonRegimeRelative M spec m F
        (eventuallyObservedProperty spec.descriptor true)
        B₁ (menu.choice i) := by
  classical
  obtain ⟨i, hi, hmax⟩ :=
    Finset.exists_max_image
      (supportEligibleIndices M spec F B₁ menu)
      (menuConstitutiveMargin M spec F B₁ menu) hne
  have he := (supportEligibleIndices_mem_iff M spec F B₁ menu i).mp hi
  have hpos : 0 < menuConstitutiveMargin M spec F B₁ menu i :=
    (margin_pos_iff_support_of_exactGR
      M spec m F B₁ menu hGR hmode i).mpr he.2
  refine ⟨i, hi, hpos, ?_, ?_⟩
  · intro j hj
    by_cases heJ : menuSupportEligible M spec F B₁ menu j
    · exact hmax j ((supportEligibleIndices_mem_iff
        M spec F B₁ menu j).mpr ⟨hj, heJ⟩)
    · have hz : menuConstitutiveMargin M spec F B₁ menu j = 0 :=
        support_ineligible_margin_zero M spec m F B₁ menu
          hGR hmode j heJ
      rw [hz]
      exact le_of_lt hpos
  · exact eligible_index_certifies_original_relativePR
      M spec m F B₁ menu hGR hmode i hi

/-- The output of a certified eligible maximum is truly an
admissible strategic intervention in the frozen declared family:
the original physical world kernel P remains fixed. -/
theorem selected_member_world_fixed
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I) (i : I) :
    (menu.choice i).intervention.apply.world = M.world :=
  (menu.choice i).world_eq

/-- True zero global maximum iff the support-eligible list is empty,
under the explicit original baseline and convergence-mode gates. -/
theorem max_margin_zero_iff_no_eligible_of_exactGR
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
    (i : I) (hi : i ∈ menu.indices)
    (hmax : ∀ j ∈ menu.indices,
      menuConstitutiveMargin M spec F B₁ menu j ≤
        menuConstitutiveMargin M spec F B₁ menu i) :
    menuConstitutiveMargin M spec F B₁ menu i = 0 ↔
      supportEligibleIndices M spec F B₁ menu = ∅ := by
  constructor
  · intro hz
    apply (empty_eligible_iff_all_listed_margin_zero_of_exactGR
      M spec m F B₁ menu hGR hmode).mpr
    intro j hj
    have hle := hmax j hj
    rw [hz] at hle
    exact le_antisymm hle (menu_margin_nonneg M spec F B₁ menu j)
  · intro hem
    exact (empty_eligible_iff_all_listed_margin_zero_of_exactGR
      M spec m F B₁ menu hGR hmode).mp hem i hi

/-- Equal exact positive support of two separately typed menu members
preserves structural eligibility; their numerical margins may differ. -/
theorem same_support_eligibility_invariant
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I)
    (i j : I)
    (hs : SamePositiveSupport
      (menu.choice i).intervention.apply.inducedKernel
      (menu.choice j).intervention.apply.inducedKernel) :
    menuSupportEligible M spec F B₁ menu i ↔
      menuSupportEligible M spec F B₁ menu j := by
  constructor
  · intro hi y hy
    exact (opposingReachability_iff_of_sameSupport
      (menu.choice i).intervention.apply.inducedKernel
      (menu.choice j).intervention.apply.inducedKernel
      spec.descriptor spec.target y hs).mp (hi y hy)
  · intro hj y hy
    exact (opposingReachability_iff_of_sameSupport
      (menu.choice i).intervention.apply.inducedKernel
      (menu.choice j).intervention.apply.inducedKernel
      spec.descriptor spec.target y hs).mpr (hj y hy)

/-- Point event mass is in [0,1] for EACH actual Markov kernel,
not just for an already certified Exact GR. -/
private theorem point_good_probability_bounds
    {Y : Type*} [MeasurableSpace Y] [Fintype Y]
    [MeasurableSingletonClass Y] [Nonempty Y]
    [DecidableEq Y] [StandardBorelSpace Y]
    (K : Kernel Y Y) [IsMarkovKernel K]
    (h : Y → Bool) (y : Y) :
    (0 : ℝ) ≤ (pointGoodMass K h y).toReal ∧
      (pointGoodMass K h y).toReal ≤ 1 := by
  have hm : pointGoodMass K h y ≤ (1 : ℝ≥0∞) := by
    rw [pointGoodMass_eq_event_probability]
    calc
      (canonicalPathLaw K (Measure.dirac y)) (eventuallyObserved h true) ≤
          (canonicalPathLaw K (Measure.dirac y)) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hf : pointGoodMass K h y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hm
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hr := (ENNReal.toReal_le_toReal hf ENNReal.one_ne_top).2 hm
  simpa using hr

/-- An ORIGINAL probability-of-event effect lies in [0,1],
regardless of GR or baseline target, because each event probability
of its separately computed actual Markov paths is in [0,1]. -/
theorem eventConstitutiveEffect_le_one
    (M : StrategicWorldModel S X A)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (h : JointState S X → Bool)
    (J : AdmissibleStrategicIntervention F)
    (y : JointState S X) :
    constitutiveEffect M (eventuallyObservedProperty h true) J y ≤ 1 := by
  have ha := point_good_probability_bounds M.inducedKernel h y
  have hb := point_good_probability_bounds
    J.intervention.apply.inducedKernel h y
  rw [effect_eq_abs_goodMass_difference M F J h y]
  apply abs_le.mpr
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- Every genuine ORIGINAL uniform probability-event constitutive
margin is bounded by ONE.  Crucially, no baseline Exact GR premise. -/
theorem eventConstitutiveMargin_le_one
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) :
    constitutiveMargin M spec F
      (eventuallyObservedProperty spec.descriptor true)
      B₁ J ≤ 1 := by
  obtain ⟨y, hy⟩ := B₁.states_nonempty
  exact (constitutiveMargin_le_effect M spec F
    (eventuallyObservedProperty spec.descriptor true) B₁ J hy).trans
      (eventConstitutiveEffect_le_one M F spec.descriptor J y)

/-- C8's G7 transfers the ORIGINAL original-PR yes/no status
across two separately admissible listed members having identical
positive-edge support. It makes NO numerical margin-equality claim. -/
theorem same_support_listed_uniformPR_iff
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (menu : FrozenMenu M F I)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool)
    (i j : I)
    (hs : SamePositiveSupport
      (menu.choice i).intervention.apply.inducedKernel
      (menu.choice j).intervention.apply.inducedKernel) :
    IsUniformGeneralizedPermanssonRegimeRelative M spec m F
      (eventuallyObservedProperty spec.descriptor true)
      B₁ (menu.choice i) ↔
    IsUniformGeneralizedPermanssonRegimeRelative M spec m F
      (eventuallyObservedProperty spec.descriptor true)
      B₁ (menu.choice j) :=
  original_uniformPR_iff_of_same_intervened_support
    M spec m F B₁ (menu.choice i) (menu.choice j) hmode hs

end MenuMarginOptimization
end ReverseSolver
end PermanssonResearch
