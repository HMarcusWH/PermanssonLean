import PermanssonResearch.MultiAgent.Protocols
import PermanssonLean.Regime.ConstitutiveMargin
import PermanssonLean.Regime.Perturbation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-!
# F1.3 — Adaptation-protocol bounds (V20.29)

For two admissible strategic interventions `J₁, J₂` of the same frozen family,
with property points `z₀(y) = ψ(P_y)`, `zᵢ(y) = ψ(P_y^{Jᵢ})`, effects
`Δᵢ(y) = d(z₀, zᵢ)` (the frozen `constitutiveEffect`) and protocol distance
`A(y) = d(z₁, z₂)`:

`|Δ₁(y) − Δ₂(y)| ≤ A(y) ≤ Δ₁(y) + Δ₂(y)`,

and `A = Δ₁` when `Δ₂ = 0` (and symmetrically). The CL/OL statement
`abs_closedLoop_sub_openLoop_le_adapt` is the specialization to the protocol
family. With a uniform gap bound over a comparison set, the ORIGINAL frozen
constitutive margins differ by at most that bound
(`abs_constitutiveMargin_sub_le_of_protocolGap`).

These are METRIC identities on property values. They are not identified
direct/indirect causal mediation effects (the OL protocol also intervenes on the
opponent), and the SIGN of `Δ_CL − Δ_OL` is not determined by `A`.
-/

namespace PermanssonResearch.MultiAgent

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

section Generic

universe uS uX uA uZ uK uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {Z : Type uZ} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace H]
variable [MetricSpace Z]

/-- Protocol distance `A(y) = d_ψ(z₁(y), z₂(y))` between two intervened outputs. -/
noncomputable def protocolGap {M : StrategicWorldModel S X A} {C : Type uK}
    {F : InterventionFamily M C} (ψ : RegimePropertyMap (JointState S X) Z)
    (J₁ J₂ : AdmissibleStrategicIntervention F) (y : JointState S X) : ℝ :=
  dist (intervenedPropertyValue ψ J₁.intervention y)
    (intervenedPropertyValue ψ J₂.intervention y)

theorem protocolGap_comm {M : StrategicWorldModel S X A} {C : Type uK}
    {F : InterventionFamily M C} (ψ : RegimePropertyMap (JointState S X) Z)
    (J₁ J₂ : AdmissibleStrategicIntervention F) (y : JointState S X) :
    protocolGap ψ J₁ J₂ y = protocolGap ψ J₂ J₁ y :=
  dist_comm _ _

/-- **V20.29, lower half.** `|Δ₁(y) − Δ₂(y)| ≤ A(y)`. -/
theorem abs_effect_sub_le_protocolGap (M : StrategicWorldModel S X A) {C : Type uK}
    {F : InterventionFamily M C} (ψ : RegimePropertyMap (JointState S X) Z)
    (J₁ J₂ : AdmissibleStrategicIntervention F) (y : JointState S X) :
    |constitutiveEffect M ψ J₁ y - constitutiveEffect M ψ J₂ y| ≤
      protocolGap ψ J₁ J₂ y := by
  unfold constitutiveEffect protocolGap
  rw [dist_comm (baselinePropertyValue ψ M y), dist_comm (baselinePropertyValue ψ M y)]
  exact abs_dist_sub_le _ _ _

/-- **V20.29, upper half.** `A(y) ≤ Δ₁(y) + Δ₂(y)`. -/
theorem protocolGap_le_effect_add (M : StrategicWorldModel S X A) {C : Type uK}
    {F : InterventionFamily M C} (ψ : RegimePropertyMap (JointState S X) Z)
    (J₁ J₂ : AdmissibleStrategicIntervention F) (y : JointState S X) :
    protocolGap ψ J₁ J₂ y ≤ constitutiveEffect M ψ J₁ y + constitutiveEffect M ψ J₂ y :=
  dist_triangle_left _ _ _

/-- If the second protocol has zero effect at `y`, the gap equals the first effect. -/
theorem protocolGap_eq_of_effect_zero (M : StrategicWorldModel S X A) {C : Type uK}
    {F : InterventionFamily M C} (ψ : RegimePropertyMap (JointState S X) Z)
    (J₁ J₂ : AdmissibleStrategicIntervention F) (y : JointState S X)
    (h : constitutiveEffect M ψ J₂ y = 0) :
    protocolGap ψ J₁ J₂ y = constitutiveEffect M ψ J₁ y := by
  unfold constitutiveEffect at h ⊢
  unfold protocolGap
  rw [dist_eq_zero.mp h, dist_comm]

/-- If the first protocol has zero effect at `y`, the gap equals the second effect. -/
theorem protocolGap_eq_of_effect_zero_left (M : StrategicWorldModel S X A) {C : Type uK}
    {F : InterventionFamily M C} (ψ : RegimePropertyMap (JointState S X) Z)
    (J₁ J₂ : AdmissibleStrategicIntervention F) (y : JointState S X)
    (h : constitutiveEffect M ψ J₁ y = 0) :
    protocolGap ψ J₁ J₂ y = constitutiveEffect M ψ J₂ y := by
  rw [protocolGap_comm]
  exact protocolGap_eq_of_effect_zero M ψ J₂ J₁ y h

/-- **V20.29, margin level (uniform gap).** If the protocol distance is at most
`G` on every comparison state, the two ORIGINAL constitutive margins differ by at
most `G`. No pointwise direction (`Δ₁ ≥ Δ₂`) is asserted. -/
theorem abs_constitutiveMargin_sub_le_of_protocolGap
    (M : StrategicWorldModel S X A) (spec : RegimeSpecification (JointState S X) H)
    {C : Type uK} (F : InterventionFamily M C) (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) (J₁ J₂ : AdmissibleStrategicIntervention F)
    {G : ℝ} (hG : ∀ y ∈ B₁.states, protocolGap ψ J₁ J₂ y ≤ G) :
    |constitutiveMargin M spec F ψ B₁ J₁ - constitutiveMargin M spec F ψ B₁ J₂| ≤ G := by
  obtain ⟨y₁, hy₁, -⟩ := B₁.pathLawNontrivial
  exact abs_sInf_image_sub_sInf_image_le_of_uniform B₁.states ⟨y₁, hy₁⟩ _ _
    (fun y _ => constitutiveEffect_nonneg M ψ J₁ y)
    (fun y _ => constitutiveEffect_nonneg M ψ J₂ y)
    (fun y hy => (abs_effect_sub_le_protocolGap M ψ J₁ J₂ y).trans (hG y hy))

end Generic

section Protocols

universe u0 u1 u2 uX uA1 uA2 uZ
variable {S0 : Type u0} {S1 : Type u1} {S2 : Type u2} {X : Type uX}
variable {A1 : Type uA1} {A2 : Type uA2} {Z : Type uZ}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]
variable [MetricSpace Z]

/-- **F1.3 (spec name).** For the declared CL and OL protocols of player 1:
`|Δ_CL(y) − Δ_OL(y)| ≤ A₁(y) ≤ Δ_CL(y) + Δ_OL(y)`, with `A₁ = d_ψ(z_CL, z_OL)`. -/
theorem abs_closedLoop_sub_openLoop_le_adapt (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerOneMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerTwoMechanism S0 S1 S2 X A1 A2))
    (a : PlayerTwoMechanism S0 S1 S2 X A1 A2) (ha : a ∈ anchors)
    (ψ : RegimePropertyMap (JointState (GameState S0 S1 S2) X) Z)
    (y : JointState (GameState S0 S1 S2) X) :
    |constitutiveEffect (G.toModel P) ψ (closedLoopIntervention G P r anchors) y -
        constitutiveEffect (G.toModel P) ψ (openLoopIntervention G P r anchors a ha) y| ≤
      protocolGap ψ (closedLoopIntervention G P r anchors)
        (openLoopIntervention G P r anchors a ha) y ∧
    protocolGap ψ (closedLoopIntervention G P r anchors)
        (openLoopIntervention G P r anchors a ha) y ≤
      constitutiveEffect (G.toModel P) ψ (closedLoopIntervention G P r anchors) y +
        constitutiveEffect (G.toModel P) ψ (openLoopIntervention G P r anchors a ha) y :=
  ⟨abs_effect_sub_le_protocolGap _ ψ _ _ y, protocolGap_le_effect_add _ ψ _ _ y⟩

end Protocols

end PermanssonResearch.MultiAgent
