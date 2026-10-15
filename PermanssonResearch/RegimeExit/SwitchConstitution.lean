import PermanssonResearch.RegimeExit.SwitchProperty
import PermanssonLean.Regime.ConstitutiveMargin
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# C-Exit B — PR66 first-exit routing implies ORIGINAL full-path constitution

No independently assumed survival gap, no alternative constitutive
functional, and no positive-margin claim at eta=1. The bound is obtained
from actual PR66 probability conservation, not a finite-horizon surrogate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH uT uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {T : Type uT}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MeasurableSpace T]
variable [TopologicalSpace S] [TopologicalSpace X]

/-- Destination basin is outside the source region; true first-exit routing
to a target is dominated by all outside destinations. -/
theorem switch_target_route_le_all_exit
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (J : AdmissibleStrategicIntervention F)
    (hDisjoint : Disjoint source.region target.region)
    (y : JointState S X) :
    exitRoutingInfinite J.intervention.apply source y target.basin ≤
      exitRoutingInfinite J.intervention.apply source y
        (Set.univ \ source.region) := by
  have hsubset : target.basin ⊆ Set.univ \ source.region := by
    intro z hz
    refine ⟨Set.mem_univ z, ?_⟩
    intro hsource
    exact Set.disjoint_left.mp hDisjoint hsource
      (target.basin_subset_region hz)
  change
    (exitRoutingInfiniteMeasure J.intervention.apply source y)
        target.basin ≤
      (exitRoutingInfiniteMeasure J.intervention.apply source y)
        (Set.univ \ source.region)
  exact measure_mono hsubset

/-- Bound the actual intervened original-region survival probability.
The proof uses PR66 infinite probability conservation and the frozen
target first-exit event, converting the finite ENNReal probabilities
to real numbers only AFTER proving finiteness. -/
theorem switch_intervened_survival_real_le
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (eta : ℝ≥0∞)
    (hBound : SwitchRoutingBound M source target F B₁ J eta)
    {y : JointState S X} (hy : y ∈ B₁.states) :
    (survivalForeverProbability J.intervention.apply source y).toReal ≤
      eta.toReal := by
  have hinside : y ∈ source.region :=
    ConstitutiveComparisonSet.states_subset_region M source B₁ hy
  have hrouteLe :=
    switch_target_route_le_all_exit M source target F J
      cert.disjointRegions y
  have hTargetFinite :
      exitRoutingInfinite J.intervention.apply source y target.basin ≠ ⊤ := by
    rw [exitRoutingInfinite_eq_prob_exit_in J.intervention.apply
      source hinside target.basin target.basin_measurable]
    exact measure_ne_top _ _
  have hAllFinite :
      exitRoutingInfinite J.intervention.apply source y
        (Set.univ \ source.region) ≠ ⊤ := by
    rw [exitRoutingInfinite_eq_prob_exit_in J.intervention.apply source
      hinside (Set.univ \ source.region)
        (MeasurableSet.univ.diff source.region_measurable)]
    exact measure_ne_top _ _
  have hSurvivalFinite :
      survivalForeverProbability J.intervention.apply source y ≠ ⊤ := by
    change J.intervention.apply.pathLaw (Measure.dirac y)
      (survivesForeverSet source) ≠ ⊤
    exact measure_ne_top _ _
  have hsum :
      (exitRoutingInfinite J.intervention.apply source y
          (Set.univ \ source.region)).toReal +
        (survivalForeverProbability J.intervention.apply source y).toReal = 1 := by
    have h := congrArg ENNReal.toReal
      (exitRoutingInfinite_add_survivalForever_eq_one
        J.intervention.apply source hinside)
    rw [ENNReal.toReal_add hAllFinite hSurvivalFinite] at h
    simpa using h
  have hLower :
      1 - eta.toReal ≤
        (exitRoutingInfinite J.intervention.apply source y target.basin).toReal := by
    have h := ENNReal.toReal_mono hTargetFinite (hBound.2 y hy)
    rw [ENNReal.toReal_sub_of_le hBound.1 (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)] at h
    simpa using h
  have hTargetLeAll :
      (exitRoutingInfinite J.intervention.apply source y target.basin).toReal ≤
        (exitRoutingInfinite J.intervention.apply source y
          (Set.univ \ source.region)).toReal :=
    ENNReal.toReal_mono hAllFinite hrouteLe
  linarith

/-- Pointwise effect is on the original real path-law property and is at
least the actual first-exit routing gap from every B1 comparison state. -/
theorem switch_constitutive_effect_ge
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (eta : ℝ≥0∞)
    (hBound : SwitchRoutingBound M source target F B₁ J eta)
    {y : JointState S X} (hy : y ∈ B₁.states) :
    1 - eta.toReal ≤
      constitutiveEffect M (switchSurvivalProperty source) J y := by
  have hSurvival :=
    switch_intervened_survival_real_le M source target
      mSource mTarget F B₁ J cert eta hBound hy
  have hEtaReal : eta.toReal ≤ (1 : ℝ) := by
    have h := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
      hBound.1
    simpa using h
  have hAbs :
      0 ≤ 1 - (survivalForeverProbability J.intervention.apply source y).toReal := by
    linarith
  unfold constitutiveEffect
  rw [switch_baseline_property_one M source target
    mSource mTarget F B₁ J cert hy,
    switch_intervened_property_eq_actual_survival M source F J y]
  rw [Real.dist_eq, abs_of_nonneg hAbs]
  linarith

/-- The genuine original uniform constitutive margin has a common lower
bound 1 - eta; existence of a comparison state is built into B1. -/
theorem switch_constitutive_margin_ge
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (eta : ℝ≥0∞)
    (hBound : SwitchRoutingBound M source target F B₁ J eta) :
    1 - eta.toReal ≤ constitutiveMargin M source F
      (switchSurvivalProperty source) B₁ J := by
  unfold constitutiveMargin
  apply le_csInf
  · obtain ⟨y, hy⟩ := B₁.states_nonempty M source
    exact ⟨_, ⟨y, hy, rfl⟩⟩
  · rintro z ⟨y, hy, rfl⟩
    exact switch_constitutive_effect_ge M source target
      mSource mTarget F B₁ J cert eta hBound hy

/-- A strictly better-than-vacuous routing guarantee establishes genuine
uniform strategic constitution under the original PR predicate. -/
theorem switch_uniformly_strategically_constitutive
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (eta : ℝ≥0∞)
    (hBound : SwitchRoutingBound M source target F B₁ J eta)
    (hEta : eta < 1) :
    IsUniformlyStrategicallyConstitutive M source F
      (switchSurvivalProperty source) B₁ J := by
  have hEtaReal : eta.toReal < (1 : ℝ) := by
    have h := ENNReal.toReal_strict_mono
      (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hEta
    simpa using h
  apply (uniformlyConstitutive_iff_margin_pos M source F
    (switchSurvivalProperty source) B₁ J).2
  have hGap := switch_constitutive_margin_ge M source target
    mSource mTarget F B₁ J cert eta hBound
  linarith

end PermanssonResearch.RegimeExit
