import PermanssonResearch.RegimeExit.SwitchConstitution
import PermanssonLean.Regime.GroundedUniformPermansson
import Mathlib.Tactic

/-!
# C-Exit B — actual grounded confirmatory PR bridge

The route/margin theorem alone is not a confirmatory PR. This bridge
requires the existing independent descriptor-nondegenerate confirmatory
GR certificate and the original SAME-PROTOCOL grounded property
factorization. Neither is redefined, omitted, or postulated as trivial.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH uT uG uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {T : Type uT} {G : Type uG}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MeasurableSpace T] [MeasurableSpace G]
variable [TopologicalSpace S] [TopologicalSpace X]

/-- Explicit confirmatory PR bridge, with no substitute constitutive
definition. All three original PR_g clauses are separately discharged.
The target is an independently exact GR, not assumed confirmatory. -/
theorem switch_grounded_confirmatory_uniformPR
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
    (hEta : eta < 1)
    (g : GroundedRelevanceMap source G)
    (hConfirmatory : IsConfirmatoryGeneratedRegime M source mSource)
    (hGrounded : IsGroundedPropertyRelative M source F
      (switchSurvivalProperty source) g J) :
    IsGroundedConfirmatoryUniformPermanssonRegimeRelative
      M source mSource F (switchSurvivalProperty source) g B₁ J := by
  exact ⟨hConfirmatory,
    switch_uniformly_strategically_constitutive M source target
      mSource mTarget F B₁ J cert eta hBound hEta,
    hGrounded⟩

/-- In particular, the same conditions prove ORIGINAL strategically
constitutive behaviour without demanding a positive alternative-margin
predicate invented in research code. -/
theorem switch_original_strategic_constitution
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
    IsStrategicallyConstitutive M source F
      (switchSurvivalProperty source) B₁ J := by
  exact uniformlyConstitutive_implies_constitutive M source F
    (switchSurvivalProperty source) B₁ J
      (switch_uniformly_strategically_constitutive M source target
        mSource mTarget F B₁ J cert eta hBound hEta)

end PermanssonResearch.RegimeExit
