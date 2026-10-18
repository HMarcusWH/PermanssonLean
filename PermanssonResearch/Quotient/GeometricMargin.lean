import PermanssonResearch.Quotient.GeometricQuotient
import PermanssonResearch.Quotient.ApproxMargin
import PermanssonLean.Regime.UniformPermansson
import PermanssonLean.Regime.GroundedUniformPermansson

/-! Q-GEOMETRIC margin transport and Q-REGIME with independent original GR
certificates. The comparison domain and property are the original objects. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Quotient

open PermanssonLean PermanssonLean.ProbabilitySupport PermanssonLean.RegimeSpecification
open PermanssonResearch.Perturbation

variable {S X A Sb Xb Ab Z H Hb : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace Sb] [MeasurableSpace Xb] [MeasurableSpace Ab]
variable [MeasurableSpace H] [MeasurableSpace Hb] [MetricSpace Z]
variable [MeasurableSpace.CountableOrCountablyGenerated (JointState S X) (JointState Sb Xb)]

theorem geometricQuotient_value_dist_le
    (Qc : TypeRespectingStateCompression S X Sb Xb) {T : ℕ}
    (p : TVLipschitzPrefixProperty (JointState Sb Xb) Z T)
    (M : StrategicWorldModel S X A) (Mbar : StrategicWorldModel Sb Xb Ab)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hdef : ApproxKernelIntertwines Qc M Mbar η) (y : JointState S X) :
    dist (projectedPrefixProperty Qc p (pathProbability M (diracProba y)))
      (p.toRegimeProperty (pathProbability Mbar (diracProba (Qc.stateMap y)))) ≤
      p.constant * (1 - (1 - η) ^ T) := by
  letI := StrategicWorldModel.inducedKernel_isMarkov M
  letI := StrategicWorldModel.inducedKernel_isMarkov Mbar
  rw [projectedPrefixProperty_value, coarsePrefixProperty_value]
  exact (p.lipschitz _ _).trans (mul_le_mul_of_nonneg_left
    (approxQuotient_prefix_tv_le_geometric Qc.stateMap_measurable _ _ hη0 hη1 hdef y T)
    p.constant_nonneg)

theorem geometricQuotient_effect_abs_le
    (Qc : TypeRespectingStateCompression S X Sb Xb) {T : ℕ}
    (p : TVLipschitzPrefixProperty (JointState Sb Xb) Z T)
    {M : StrategicWorldModel S X A} {Mbar : StrategicWorldModel Sb Xb Ab}
    {Component ComponentBar : Type*}
    {F : InterventionFamily M Component} {Fbar : InterventionFamily Mbar ComponentBar}
    (J : AdmissibleStrategicIntervention F) (Jbar : AdmissibleStrategicIntervention Fbar)
    {η₀ ηJ : ℝ} (h₀ : 0 ≤ η₀) (h₀1 : η₀ ≤ 1) (hJ : 0 ≤ ηJ) (hJ1 : ηJ ≤ 1)
    (hdef₀ : ApproxKernelIntertwines Qc M Mbar η₀)
    (hdefJ : ApproxKernelIntertwines Qc J.intervention.apply Jbar.intervention.apply ηJ)
    (y : JointState S X) :
    |constitutiveEffect M (projectedPrefixProperty Qc p) J y -
      constitutiveEffect Mbar p.toRegimeProperty Jbar (Qc.stateMap y)| ≤
      p.constant * ((1 - (1 - η₀) ^ T) + (1 - (1 - ηJ) ^ T)) := by
  unfold constitutiveEffect baselinePropertyValue intervenedPropertyValue
  rw [mul_add]
  exact (abs_dist_sub_dist_le _ _ _ _).trans (add_le_add
    (geometricQuotient_value_dist_le Qc p M Mbar h₀ h₀1 hdef₀ y)
    (geometricQuotient_value_dist_le Qc p _ _ hJ hJ1 hdefJ y))

theorem geometricQuotient_margin_abs_le
    (Qc : TypeRespectingStateCompression S X Sb Xb) {T : ℕ}
    (p : TVLipschitzPrefixProperty (JointState Sb Xb) Z T)
    {M : StrategicWorldModel S X A} {Mbar : StrategicWorldModel Sb Xb Ab}
    (spec : RegimeSpecification (JointState S X) H)
    (specBar : RegimeSpecification (JointState Sb Xb) Hb)
    {Component ComponentBar : Type*}
    (F : InterventionFamily M Component) (Fbar : InterventionFamily Mbar ComponentBar)
    (B₁ : ConstitutiveComparisonSet M spec) (B₁bar : ConstitutiveComparisonSet Mbar specBar)
    (hB : B₁bar.states = Qc.stateMap '' B₁.states)
    (J : AdmissibleStrategicIntervention F) (Jbar : AdmissibleStrategicIntervention Fbar)
    {η₀ ηJ : ℝ} (h₀ : 0 ≤ η₀) (h₀1 : η₀ ≤ 1) (hJ : 0 ≤ ηJ) (hJ1 : ηJ ≤ 1)
    (hdef₀ : ApproxKernelIntertwines Qc M Mbar η₀)
    (hdefJ : ApproxKernelIntertwines Qc J.intervention.apply Jbar.intervention.apply ηJ) :
    |constitutiveMargin M spec F (projectedPrefixProperty Qc p) B₁ J -
      constitutiveMargin Mbar specBar Fbar p.toRegimeProperty B₁bar Jbar| ≤
      p.constant * ((1 - (1 - η₀) ^ T) + (1 - (1 - ηJ) ^ T)) := by
  unfold constitutiveMargin
  rw [hB, ← Set.image_comp]
  obtain ⟨y₁, hy₁, -⟩ := B₁.pathLawNontrivial
  exact abs_sInf_image_sub_sInf_image_le_of_uniform B₁.states ⟨y₁, hy₁⟩ _ _
    (fun _ _ => dist_nonneg) (fun _ _ => dist_nonneg)
    (fun y _ => geometricQuotient_effect_abs_le Qc p J Jbar h₀ h₀1 hJ hJ1 hdef₀ hdefJ y)

/-- Original PR on both sides requires both independently established original
Exact-GR certificates. A quotient defect alone supplies neither certificate. -/
theorem geometricQuotient_uniformPR_pair
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Sb] [TopologicalSpace Xb]
    (Qc : TypeRespectingStateCompression S X Sb Xb) {T : ℕ}
    (p : TVLipschitzPrefixProperty (JointState Sb Xb) Z T)
    {M : StrategicWorldModel S X A} {Mbar : StrategicWorldModel Sb Xb Ab}
    (spec : RegimeSpecification (JointState S X) H)
    (specBar : RegimeSpecification (JointState Sb Xb) Hb)
    (m : Measure (JointState S X)) (mbar : Measure (JointState Sb Xb))
    (hGR : IsExactGeneratedRegime M spec m) (hGRbar : IsExactGeneratedRegime Mbar specBar mbar)
    {Component ComponentBar : Type*}
    (F : InterventionFamily M Component) (Fbar : InterventionFamily Mbar ComponentBar)
    (B₁ : ConstitutiveComparisonSet M spec) (B₁bar : ConstitutiveComparisonSet Mbar specBar)
    (hB : B₁bar.states = Qc.stateMap '' B₁.states)
    (J : AdmissibleStrategicIntervention F) (Jbar : AdmissibleStrategicIntervention Fbar)
    {η₀ ηJ : ℝ} (h₀ : 0 ≤ η₀) (h₀1 : η₀ ≤ 1) (hJ : 0 ≤ ηJ) (hJ1 : ηJ ≤ 1)
    (hdef₀ : ApproxKernelIntertwines Qc M Mbar η₀)
    (hdefJ : ApproxKernelIntertwines Qc J.intervention.apply Jbar.intervention.apply ηJ)
    (hgap : p.constant * ((1 - (1 - η₀) ^ T) + (1 - (1 - ηJ) ^ T)) <
      constitutiveMargin M spec F (projectedPrefixProperty Qc p) B₁ J) :
    IsUniformGeneralizedPermanssonRegimeRelative M spec m F (projectedPrefixProperty Qc p) B₁ J ∧
    IsUniformGeneralizedPermanssonRegimeRelative Mbar specBar mbar Fbar p.toRegimeProperty B₁bar Jbar := by
  have hbudget : 0 ≤ p.constant * ((1 - (1 - η₀) ^ T) + (1 - (1 - ηJ) ^ T)) :=
    mul_nonneg p.constant_nonneg (add_nonneg
      (geometricTVEnvelope_nonneg h₀ h₀1 T) (geometricTVEnvelope_nonneg hJ hJ1 T))
  have hfine : 0 < constitutiveMargin M spec F (projectedPrefixProperty Qc p) B₁ J :=
    hbudget.trans_lt hgap
  have h := geometricQuotient_margin_abs_le Qc p spec specBar F Fbar B₁ B₁bar hB
    J Jbar h₀ h₀1 hJ hJ1 hdef₀ hdefJ
  have hcoarse : 0 < constitutiveMargin Mbar specBar Fbar p.toRegimeProperty B₁bar Jbar := by
    rw [abs_le] at h
    linarith [h.2]
  exact ⟨⟨hGR, (uniformlyConstitutive_iff_margin_pos _ _ _ _ _ _).mpr hfine⟩,
    ⟨hGRbar, (uniformlyConstitutive_iff_margin_pos _ _ _ _ _ _).mpr hcoarse⟩⟩

/-- Either side can supply the strict gap. Bare positivity is insufficient
when the budget is positive. -/
theorem margin_positive_pair_of_budget {a b e : ℝ} (he : 0 ≤ e)
    (hab : |a - b| ≤ e) (hgap : e < a ∨ e < b) : 0 < a ∧ 0 < b := by
  rw [abs_le] at hab
  rcases hgap with h | h <;> constructor <;> linarith

/-- Independent original confirmatory and grounding gates can be combined
with any proved original-margin budget, in either direction. Applying the
geometric margin theorem supplies that budget without supplying these gates. -/
theorem grounded_uniformPR_pair_of_margin_budget
    {G Gb Component ComponentBar : Type*} [MeasurableSpace G] [MeasurableSpace Gb]
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Sb] [TopologicalSpace Xb]
    (M : StrategicWorldModel S X A) (Mbar : StrategicWorldModel Sb Xb Ab)
    (spec : RegimeSpecification (JointState S X) H)
    (specBar : RegimeSpecification (JointState Sb Xb) Hb)
    (m : Measure (JointState S X)) (mbar : Measure (JointState Sb Xb))
    (F : InterventionFamily M Component) (Fbar : InterventionFamily Mbar ComponentBar)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (ψbar : RegimePropertyMap (JointState Sb Xb) Z)
    (g : GroundedRelevanceMap spec G) (gbar : GroundedRelevanceMap specBar Gb)
    (B₁ : ConstitutiveComparisonSet M spec) (B₁bar : ConstitutiveComparisonSet Mbar specBar)
    (J : AdmissibleStrategicIntervention F) (Jbar : AdmissibleStrategicIntervention Fbar)
    (hconfirm : IsConfirmatoryGeneratedRegime M spec m)
    (hconfirmBar : IsConfirmatoryGeneratedRegime Mbar specBar mbar)
    (hground : IsGroundedPropertyRelative M spec F ψ g J)
    (hgroundBar : IsGroundedPropertyRelative Mbar specBar Fbar ψbar gbar Jbar)
    {e : ℝ} (he : 0 ≤ e)
    (hbudget : |constitutiveMargin M spec F ψ B₁ J -
      constitutiveMargin Mbar specBar Fbar ψbar B₁bar Jbar| ≤ e)
    (hgap : e < constitutiveMargin M spec F ψ B₁ J ∨
      e < constitutiveMargin Mbar specBar Fbar ψbar B₁bar Jbar) :
    IsGroundedConfirmatoryUniformPermanssonRegimeRelative M spec m F ψ g B₁ J ∧
    IsGroundedConfirmatoryUniformPermanssonRegimeRelative
      Mbar specBar mbar Fbar ψbar gbar B₁bar Jbar := by
  have hpos := margin_positive_pair_of_budget he hbudget hgap
  exact ⟨⟨hconfirm, (uniformlyConstitutive_iff_margin_pos _ _ _ _ _ _).mpr hpos.1, hground⟩,
    ⟨hconfirmBar, (uniformlyConstitutive_iff_margin_pos _ _ _ _ _ _).mpr hpos.2, hgroundBar⟩⟩

end PermanssonResearch.Quotient
