import PermanssonLean.Regime.Constitution
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open MeasureTheory ProbabilityTheory Set

namespace PermanssonLean

universe uS uX uA uH uZ uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
variable [MetricSpace Z]

namespace RegimeSpecification

/-- Pointwise constitutive effect
\[
\Delta_{\psi,J}(y)
=
d_\psi\bigl(\psi(P_y),\psi(P_y^J)\bigr).
\]
-/
noncomputable def constitutiveEffect
    (M : StrategicWorldModel S X A)
    {Component : Type uK}
    {F : InterventionFamily M Component}
    (ψ : RegimePropertyMap (JointState S X) Z)
    (J : AdmissibleStrategicIntervention F)
    (y : JointState S X) : ℝ :=
  dist
    (baselinePropertyValue ψ M y)
    (intervenedPropertyValue ψ J.intervention y)

/-- Uniform constitutive margin
\[
\kappa_{\psi,J}(B_1)
=
\inf_{y\in B_1}\Delta_{\psi,J}(y).
\]
The comparison set is nonempty by construction, and the effect set is bounded
below by zero.
-/
noncomputable def constitutiveMargin
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) : ℝ :=
  sInf (constitutiveEffect M ψ J '' B₁.states)

theorem constitutiveEffect_nonneg
    (M : StrategicWorldModel S X A)
    {Component : Type uK}
    {F : InterventionFamily M Component}
    (ψ : RegimePropertyMap (JointState S X) Z)
    (J : AdmissibleStrategicIntervention F)
    (y : JointState S X) :
    0 ≤ constitutiveEffect M ψ J y := by
  unfold constitutiveEffect
  exact dist_nonneg

theorem constitutiveEffect_pos_iff
    (M : StrategicWorldModel S X A)
    {Component : Type uK}
    {F : InterventionFamily M Component}
    (ψ : RegimePropertyMap (JointState S X) Z)
    (J : AdmissibleStrategicIntervention F)
    (y : JointState S X) :
    0 < constitutiveEffect M ψ J y ↔
      baselinePropertyValue ψ M y ≠
        intervenedPropertyValue ψ J.intervention y := by
  unfold constitutiveEffect
  exact dist_pos

theorem constitutiveMargin_nonneg
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) :
    0 ≤ constitutiveMargin M spec F ψ B₁ J := by
  unfold constitutiveMargin
  refine le_csInf ?_ ?_
  · rcases B₁.states_nonempty with ⟨y, hy⟩
    exact ⟨constitutiveEffect M ψ J y, ⟨y, hy, rfl⟩⟩
  · intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    exact constitutiveEffect_nonneg M ψ J y

theorem constitutiveMargin_le_effect
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    {y : JointState S X}
    (hy : y ∈ B₁.states) :
    constitutiveMargin M spec F ψ B₁ J ≤ constitutiveEffect M ψ J y := by
  unfold constitutiveMargin
  refine csInf_le ?_ ⟨y, hy, rfl⟩
  refine ⟨0, ?_⟩
  rintro r ⟨z, hz, rfl⟩
  exact constitutiveEffect_nonneg M ψ J z

theorem strategicallyConstitutive_iff_effect_pos
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) :
    IsStrategicallyConstitutive M spec F ψ B₁ J ↔
      ∀ y ∈ B₁.states, 0 < constitutiveEffect M ψ J y := by
  constructor
  · intro h y hy
    exact (constitutiveEffect_pos_iff M ψ J y).2 (h y hy)
  · intro h y hy
    exact (constitutiveEffect_pos_iff M ψ J y).1 (h y hy)

/-- Equation (16): uniform strategic constitution means that one strictly
positive lower bound works across the whole frozen comparison set. -/
def IsUniformlyStrategicallyConstitutive
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) : Prop :=
  ∃ δ : ℝ,
    0 < δ ∧
    δ ≤ constitutiveMargin M spec F ψ B₁ J

theorem uniformlyConstitutive_iff_margin_pos
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) :
    IsUniformlyStrategicallyConstitutive M spec F ψ B₁ J ↔
      0 < constitutiveMargin M spec F ψ B₁ J := by
  constructor
  · rintro ⟨δ, hδ, hδκ⟩
    exact lt_of_lt_of_le hδ hδκ
  · intro hκ
    exact ⟨constitutiveMargin M spec F ψ B₁ J, hκ, le_rfl⟩

theorem uniformlyConstitutive_implies_constitutive
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsUniformlyStrategicallyConstitutive M spec F ψ B₁ J) :
    IsStrategicallyConstitutive M spec F ψ B₁ J := by
  rw [strategicallyConstitutive_iff_effect_pos]
  intro y hy
  have hκ : 0 < constitutiveMargin M spec F ψ B₁ J :=
    (uniformlyConstitutive_iff_margin_pos M spec F ψ B₁ J).1 h
  exact lt_of_lt_of_le hκ (constitutiveMargin_le_effect M spec F ψ B₁ J hy)

end RegimeSpecification

end PermanssonLean
