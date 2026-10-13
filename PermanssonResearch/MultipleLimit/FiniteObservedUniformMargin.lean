import PermanssonResearch.MultipleLimit.TypedObservedEventConstitution
import PermanssonLean.Regime.UniformPermansson
import Mathlib.Tactic

/-!
# C7-04 — original unweakened finite uniformly constitutive PR iff

Finite comparison sets have an ATTAINED minimum of original constitutive
effects. Baseline Exact GR and the frozen admissible comparison-set gates
remain completely independent; eventual-event response never promotes
an invalid Exact GR into a PR.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteObservedUniformMargin

open PermanssonLean
open PermanssonLean.RegimeSpecification
open FrozenObservedEvent
open TypedObservedEventConstitution

variable {S X A H : Type*}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace A] [MeasurableSpace H]
variable [TopologicalSpace S] [TopologicalSpace X]
variable [Fintype (JointState S X)] [Nonempty (JointState S X)]
variable [DecidableEq (JointState S X)]
variable [MeasurableSingletonClass (JointState S X)]
variable [StandardBorelSpace (JointState S X)]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- A finite, genuinely nonempty ORIGINAL comparison set has an
attained constitutive margin; no claim for arbitrary infinite sets. -/
theorem finite_margin_attained
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) ℝ)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) :
    ∃ y ∈ B₁.states,
      constitutiveMargin M spec F ψ B₁ J =
        constitutiveEffect M ψ J y := by
  classical
  obtain ⟨x, hx⟩ := B₁.states_nonempty
  letI : Nonempty {y : JointState S X // y ∈ B₁.states} :=
    ⟨⟨x, hx⟩⟩
  obtain ⟨v, hv⟩ := Finite.exists_min
    (fun p : {y : JointState S X // y ∈ B₁.states} =>
      constitutiveEffect M ψ J p.val)
  refine ⟨v.val, v.property, ?_⟩
  apply le_antisymm
  · exact constitutiveMargin_le_effect M spec F ψ B₁ J v.property
  · unfold constitutiveMargin
    apply le_csInf
    · exact ⟨_, ⟨x, hx, rfl⟩⟩
    · rintro z ⟨y, hy, rfl⟩
      exact hv ⟨y, hy⟩

/-- Exact finite pointwise/positive uniform margin equivalence. -/
theorem finite_margin_pos_iff_pointwise
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) ℝ)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) :
    0 < constitutiveMargin M spec F ψ B₁ J ↔
      ∀ y ∈ B₁.states, 0 < constitutiveEffect M ψ J y := by
  constructor
  · intro h y hy
    exact lt_of_lt_of_le h
      (constitutiveMargin_le_effect M spec F ψ B₁ J hy)
  · intro h
    obtain ⟨y, hy, hmin⟩ :=
      finite_margin_attained M spec F ψ B₁ J
    rw [hmin]
    exact h y hy

/-- The exact ORIGINAL quantitative relative PR predicate,
characterized by unequal model-specific fixed-event probabilities
on every state of the declared finite comparison set. -/
theorem uniformRelativePR_iff_finite_event_response
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) :
    IsUniformGeneralizedPermanssonRegimeRelative M spec m F
      (eventuallyObservedProperty spec.descriptor true) B₁ J ↔
      IsExactGeneratedRegime M spec m ∧
      ∀ y ∈ B₁.states,
        (pointGoodMass M.inducedKernel spec.descriptor y).toReal ≠
          (pointGoodMass J.intervention.apply.inducedKernel
            spec.descriptor y).toReal := by
  constructor
  · rintro ⟨hGR, hUniform⟩
    refine ⟨hGR, ?_⟩
    have hpositive : 0 < constitutiveMargin M spec F
        (eventuallyObservedProperty spec.descriptor true) B₁ J :=
      (uniformlyConstitutive_iff_margin_pos M spec F
        (eventuallyObservedProperty spec.descriptor true) B₁ J).mp hUniform
    have hpoint := (finite_margin_pos_iff_pointwise M spec F
      (eventuallyObservedProperty spec.descriptor true) B₁ J).mp hpositive
    intro y hy
    have hne := (constitutiveEffect_pos_iff M
      (eventuallyObservedProperty spec.descriptor true) J y).mp
        (hpoint y hy)
    simpa only [baselineValue_eq_goodMass M spec.descriptor y,
      intervenedValue_eq_goodMass M F J spec.descriptor y] using hne
  · rintro ⟨hGR, hResponse⟩
    refine ⟨hGR, ?_⟩
    apply (uniformlyConstitutive_iff_margin_pos M spec F
      (eventuallyObservedProperty spec.descriptor true) B₁ J).mpr
    apply (finite_margin_pos_iff_pointwise M spec F
      (eventuallyObservedProperty spec.descriptor true) B₁ J).mpr
    intro y hy
    apply (constitutiveEffect_pos_iff M
      (eventuallyObservedProperty spec.descriptor true) J y).mpr
    simpa only [baselineValue_eq_goodMass M spec.descriptor y,
      intervenedValue_eq_goodMass M F J spec.descriptor y]
      using hResponse y hy

end FiniteObservedUniformMargin
end MultipleLimit
end PermanssonResearch
