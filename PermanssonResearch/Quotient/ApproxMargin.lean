import PermanssonResearch.Quotient.ApproxPrefix
import PermanssonResearch.Perturbation.PrimitiveLipschitz
import PermanssonLean.Regime.ConstitutiveMargin
import PermanssonLean.Regime.Perturbation
import PermanssonLean.Intervention.FrozenFamily
import Mathlib.Tactic

/-!
# E1.3 — approximate-quotient constitutive-margin comparison

A frozen `T`-prefix property on the COARSE space, `p : TVLipschitzPrefixProperty`
(an explicit functional of coarse prefix laws, `L`-Lipschitz for event TV), and its
FACTORED fine counterpart `projectedPrefixProperty Qc p`, which evaluates `p` on the
compressed fine prefix law. Factorization is part of the definition here; nothing
is inferred from small TV error.

With separate defects `η₀` (baseline) and `η_J` (matched intervention), for every
fine state `y` (spec V20.33):

  `|Δ_{ψ,J}(y) − Δ̄_{ψ̄,J̄}(q y)| ≤ L (min(1,Tη₀) + min(1,Tη_J)) ≤ L T (η₀ + η_J)`,

and for comparison sets with `B̄₁ = q(B₁)` (spec V20.34):

  `|κ_{ψ,J}(B₁) − κ̄_{ψ̄,J̄}(B̄₁)| ≤ L (min(1,Tη₀) + min(1,Tη_J))`.

The family version `approxQuotient_family_margin_abs_le` runs over a frozen label
equivalence `φ` (`QuotientFamilyMatching`), one defect per label.

## Firewalls

* A positive quotient margin is NOT an Exact-GR or PR certificate on either side;
  the Exact-GR, comparison-set and grounding gates of each model are independent
  (see `Quotient/ApproxAdversaries.lean` for the leakage counterexample).
* Whole-path, non-Lipschitz properties are not covered.
* The geometric `1 − (1 − η)^T` bound is NOT used (E1.5 OPEN).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Quotient

set_option autoImplicit false

open PermanssonLean PermanssonLean.ProbabilitySupport PermanssonLean.RegimeSpecification
open PermanssonResearch.Perturbation

universe uS uX uA uSb uXb uAb uZ uH uHb uK uKb uL uLb
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {Sb : Type uSb} {Xb : Type uXb} {Ab : Type uAb}
variable {Z : Type uZ} {H : Type uH} {Hb : Type uHb}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace Sb] [MeasurableSpace Xb] [MeasurableSpace Ab]
variable [MeasurableSpace H] [MeasurableSpace Hb] [MetricSpace Z]

/-- The fine property that FACTORS through the compressed `T`-prefix law. -/
noncomputable def projectedPrefixProperty
    (Qc : TypeRespectingStateCompression S X Sb Xb) {T : ℕ}
    (p : TVLipschitzPrefixProperty (JointState Sb Xb) Z T) :
    RegimePropertyMap (JointState S X) Z :=
  fun law => p.functional
    ((law.toMeasure.map (Preorder.frestrictLe T)).map (prefixMap Qc.stateMap T))

theorem projectedPrefixProperty_value
    (Qc : TypeRespectingStateCompression S X Sb Xb) {T : ℕ}
    (p : TVLipschitzPrefixProperty (JointState Sb Xb) Z T)
    (M : StrategicWorldModel S X A) (y : JointState S X) :
    projectedPrefixProperty Qc p (pathProbability M (diracProba y)) =
      p.functional ((finitePrefixLaw M.inducedKernel y T).map
        (prefixMap Qc.stateMap T)) := by
  change p.functional
    (((M.pathLaw (Measure.dirac y)).map (Preorder.frestrictLe T)).map
      (prefixMap Qc.stateMap T)) = _
  rw [ConstitutiveQuasi.pathLaw_finitePrefix_eq]

theorem coarsePrefixProperty_value {T : ℕ}
    (p : TVLipschitzPrefixProperty (JointState Sb Xb) Z T)
    (Mbar : StrategicWorldModel Sb Xb Ab) (x : JointState Sb Xb) :
    p.toRegimeProperty (pathProbability Mbar (diracProba x)) =
      p.functional (finitePrefixLaw Mbar.inducedKernel x T) := by
  change p.functional ((Mbar.pathLaw (Measure.dirac x)).map
    (Preorder.frestrictLe T)) = _
  rw [ConstitutiveQuasi.pathLaw_finitePrefix_eq]

/-- Property-value comparison for one matched model pair. -/
theorem approxQuotient_value_dist_le
    (Qc : TypeRespectingStateCompression S X Sb Xb) {T : ℕ}
    (p : TVLipschitzPrefixProperty (JointState Sb Xb) Z T)
    (M : StrategicWorldModel S X A) (Mbar : StrategicWorldModel Sb Xb Ab)
    {η : ℝ} (hη : 0 ≤ η) (hdef : ApproxKernelIntertwines Qc M Mbar η)
    (y : JointState S X) :
    dist (projectedPrefixProperty Qc p (pathProbability M (diracProba y)))
      (p.toRegimeProperty (pathProbability Mbar (diracProba (Qc.stateMap y)))) ≤
      p.constant * min 1 (T * η) := by
  letI := StrategicWorldModel.inducedKernel_isMarkov M
  letI := StrategicWorldModel.inducedKernel_isMarkov Mbar
  rw [projectedPrefixProperty_value, coarsePrefixProperty_value]
  exact (p.lipschitz _ _).trans (mul_le_mul_of_nonneg_left
    (approxQuotient_prefix_tv_le_min Qc.stateMap_measurable _ _ hη hdef y T)
    p.constant_nonneg)

/-- Four-point metric inequality used for effects. -/
theorem abs_dist_sub_dist_le (a b c d : Z) :
    |dist a b - dist c d| ≤ dist a c + dist b d := by
  have := dist_dist_dist_le a b c d
  rwa [Real.dist_eq] at this

/-- **E1.3, effect form (V20.33).** -/
theorem approxQuotient_effect_abs_le
    (Qc : TypeRespectingStateCompression S X Sb Xb) {T : ℕ}
    (p : TVLipschitzPrefixProperty (JointState Sb Xb) Z T)
    {M : StrategicWorldModel S X A} {Mbar : StrategicWorldModel Sb Xb Ab}
    {Component : Type uK} {ComponentBar : Type uKb}
    {F : InterventionFamily M Component} {Fbar : InterventionFamily Mbar ComponentBar}
    (J : AdmissibleStrategicIntervention F)
    (Jbar : AdmissibleStrategicIntervention Fbar)
    {η₀ ηJ : ℝ} (h₀ : 0 ≤ η₀) (hJ : 0 ≤ ηJ)
    (hdef₀ : ApproxKernelIntertwines Qc M Mbar η₀)
    (hdefJ : ApproxKernelIntertwines Qc J.intervention.apply
      Jbar.intervention.apply ηJ)
    (y : JointState S X) :
    |constitutiveEffect M (projectedPrefixProperty Qc p) J y -
        constitutiveEffect Mbar p.toRegimeProperty Jbar (Qc.stateMap y)| ≤
      p.constant * (min 1 (T * η₀) + min 1 (T * ηJ)) := by
  unfold constitutiveEffect baselinePropertyValue intervenedPropertyValue
  rw [mul_add]
  exact (abs_dist_sub_dist_le _ _ _ _).trans (add_le_add
    (approxQuotient_value_dist_le Qc p M Mbar h₀ hdef₀ y)
    (approxQuotient_value_dist_le Qc p _ _ hJ hdefJ y))

/-- The `min(1,·)` budget is at most the linear `L T (η₀ + η_J)` budget. -/
theorem approxBudget_le_linear {L : ℝ} (hL : 0 ≤ L) (T : ℕ)
    {η₀ ηJ : ℝ} :
    L * (min 1 (T * η₀) + min 1 (T * ηJ)) ≤ L * T * (η₀ + ηJ) := by
  have := add_le_add (min_le_right (1 : ℝ) (T * η₀)) (min_le_right (1 : ℝ) (T * ηJ))
  calc
    L * (min 1 (T * η₀) + min 1 (T * ηJ)) ≤ L * (T * η₀ + T * ηJ) :=
      mul_le_mul_of_nonneg_left this hL
    _ = L * T * (η₀ + ηJ) := by ring

/-- **E1.3, margin form (V20.34).** Requires `B̄₁ = q(B₁)` exactly. -/
theorem approxQuotient_margin_abs_le
    (Qc : TypeRespectingStateCompression S X Sb Xb) {T : ℕ}
    (p : TVLipschitzPrefixProperty (JointState Sb Xb) Z T)
    {M : StrategicWorldModel S X A} {Mbar : StrategicWorldModel Sb Xb Ab}
    (spec : RegimeSpecification (JointState S X) H)
    (specBar : RegimeSpecification (JointState Sb Xb) Hb)
    {Component : Type uK} {ComponentBar : Type uKb}
    (F : InterventionFamily M Component) (Fbar : InterventionFamily Mbar ComponentBar)
    (B₁ : ConstitutiveComparisonSet M spec)
    (B₁bar : ConstitutiveComparisonSet Mbar specBar)
    (hB : B₁bar.states = Qc.stateMap '' B₁.states)
    (J : AdmissibleStrategicIntervention F)
    (Jbar : AdmissibleStrategicIntervention Fbar)
    {η₀ ηJ : ℝ} (h₀ : 0 ≤ η₀) (hJ : 0 ≤ ηJ)
    (hdef₀ : ApproxKernelIntertwines Qc M Mbar η₀)
    (hdefJ : ApproxKernelIntertwines Qc J.intervention.apply
      Jbar.intervention.apply ηJ) :
    |constitutiveMargin M spec F (projectedPrefixProperty Qc p) B₁ J -
        constitutiveMargin Mbar specBar Fbar p.toRegimeProperty B₁bar Jbar| ≤
      p.constant * (min 1 (T * η₀) + min 1 (T * ηJ)) := by
  unfold constitutiveMargin
  rw [hB, ← Set.image_comp]
  obtain ⟨y₁, hy₁, -⟩ := B₁.pathLawNontrivial
  exact abs_sInf_image_sub_sInf_image_le_of_uniform B₁.states ⟨y₁, hy₁⟩ _ _
    (fun _ _ => dist_nonneg) (fun _ _ => dist_nonneg)
    (fun y _ => approxQuotient_effect_abs_le Qc p J Jbar h₀ hJ hdef₀ hdefJ y)

/-- Positive-margin transfer: a coarse margin exceeding the full budget gives a
positive fine margin (and conversely). This is a margin statement only. -/
theorem approxQuotient_fine_margin_pos_of_coarse
    (Qc : TypeRespectingStateCompression S X Sb Xb) {T : ℕ}
    (p : TVLipschitzPrefixProperty (JointState Sb Xb) Z T)
    {M : StrategicWorldModel S X A} {Mbar : StrategicWorldModel Sb Xb Ab}
    (spec : RegimeSpecification (JointState S X) H)
    (specBar : RegimeSpecification (JointState Sb Xb) Hb)
    {Component : Type uK} {ComponentBar : Type uKb}
    (F : InterventionFamily M Component) (Fbar : InterventionFamily Mbar ComponentBar)
    (B₁ : ConstitutiveComparisonSet M spec)
    (B₁bar : ConstitutiveComparisonSet Mbar specBar)
    (hB : B₁bar.states = Qc.stateMap '' B₁.states)
    (J : AdmissibleStrategicIntervention F)
    (Jbar : AdmissibleStrategicIntervention Fbar)
    {η₀ ηJ : ℝ} (h₀ : 0 ≤ η₀) (hJ : 0 ≤ ηJ)
    (hdef₀ : ApproxKernelIntertwines Qc M Mbar η₀)
    (hdefJ : ApproxKernelIntertwines Qc J.intervention.apply
      Jbar.intervention.apply ηJ)
    (hgap : p.constant * (min 1 (T * η₀) + min 1 (T * ηJ)) <
      constitutiveMargin Mbar specBar Fbar p.toRegimeProperty B₁bar Jbar) :
    0 < constitutiveMargin M spec F (projectedPrefixProperty Qc p) B₁ J := by
  have h := approxQuotient_margin_abs_le Qc p spec specBar F Fbar B₁ B₁bar hB
    J Jbar h₀ hJ hdef₀ hdefJ
  rw [abs_le] at h
  linarith [h.1]

theorem approxQuotient_coarse_margin_pos_of_fine
    (Qc : TypeRespectingStateCompression S X Sb Xb) {T : ℕ}
    (p : TVLipschitzPrefixProperty (JointState Sb Xb) Z T)
    {M : StrategicWorldModel S X A} {Mbar : StrategicWorldModel Sb Xb Ab}
    (spec : RegimeSpecification (JointState S X) H)
    (specBar : RegimeSpecification (JointState Sb Xb) Hb)
    {Component : Type uK} {ComponentBar : Type uKb}
    (F : InterventionFamily M Component) (Fbar : InterventionFamily Mbar ComponentBar)
    (B₁ : ConstitutiveComparisonSet M spec)
    (B₁bar : ConstitutiveComparisonSet Mbar specBar)
    (hB : B₁bar.states = Qc.stateMap '' B₁.states)
    (J : AdmissibleStrategicIntervention F)
    (Jbar : AdmissibleStrategicIntervention Fbar)
    {η₀ ηJ : ℝ} (h₀ : 0 ≤ η₀) (hJ : 0 ≤ ηJ)
    (hdef₀ : ApproxKernelIntertwines Qc M Mbar η₀)
    (hdefJ : ApproxKernelIntertwines Qc J.intervention.apply
      Jbar.intervention.apply ηJ)
    (hgap : p.constant * (min 1 (T * η₀) + min 1 (T * ηJ)) <
      constitutiveMargin M spec F (projectedPrefixProperty Qc p) B₁ J) :
    0 < constitutiveMargin Mbar specBar Fbar p.toRegimeProperty B₁bar Jbar := by
  have h := approxQuotient_margin_abs_le Qc p spec specBar F Fbar B₁ B₁bar hB
    J Jbar h₀ hJ hdef₀ hdefJ
  rw [abs_le] at h
  linarith [h.2]

/-- **E1.3, frozen-family form.** Over a frozen label equivalence `φ` of the two
intervention families, with one defect per label, every label's fine margin is
within its own budget of the matched coarse label's margin. -/
theorem approxQuotient_family_margin_abs_le
    (Qc : TypeRespectingStateCompression S X Sb Xb) {T : ℕ}
    (p : TVLipschitzPrefixProperty (JointState Sb Xb) Z T)
    {M : StrategicWorldModel S X A} {Mbar : StrategicWorldModel Sb Xb Ab}
    (spec : RegimeSpecification (JointState S X) H)
    (specBar : RegimeSpecification (JointState Sb Xb) Hb)
    {Component : Type uK} {ComponentBar : Type uKb}
    {Label : Type uL} {LabelBar : Type uLb}
    (F : InterventionFamily M Component) (Fbar : InterventionFamily Mbar ComponentBar)
    (Jfam : FrozenStrategicInterventionFamily F Label)
    (Jbarfam : FrozenStrategicInterventionFamily Fbar LabelBar)
    (matching : QuotientFamilyMatching F Fbar Jfam Jbarfam)
    (B₁ : ConstitutiveComparisonSet M spec)
    (B₁bar : ConstitutiveComparisonSet Mbar specBar)
    (hB : B₁bar.states = Qc.stateMap '' B₁.states)
    {η₀ : ℝ} (h₀ : 0 ≤ η₀) (hdef₀ : ApproxKernelIntertwines Qc M Mbar η₀)
    (η : Label → ℝ) (hη : ∀ l, 0 ≤ η l)
    (hdef : ∀ l, ApproxKernelIntertwines Qc (Jfam.intervention l).intervention.apply
      (Jbarfam.intervention (matching.labelEquiv l)).intervention.apply (η l))
    (l : Label) :
    |constitutiveMargin M spec F (projectedPrefixProperty Qc p) B₁
          (Jfam.intervention l) -
        constitutiveMargin Mbar specBar Fbar p.toRegimeProperty B₁bar
          (Jbarfam.intervention (matching.labelEquiv l))| ≤
      p.constant * (min 1 (T * η₀) + min 1 (T * η l)) :=
  approxQuotient_margin_abs_le Qc p spec specBar F Fbar B₁ B₁bar hB _ _
    h₀ (hη l) hdef₀ (hdef l)

end PermanssonResearch.Quotient
