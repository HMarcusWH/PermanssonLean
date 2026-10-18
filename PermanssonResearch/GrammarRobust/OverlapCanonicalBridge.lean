import PermanssonResearch.GrammarRobust.OverlapKernelAssembly
import PermanssonLean.Regime.ConstitutiveMargin

/-! B-OVERLAP as original admissible joint-strategic interventions and margins.
Admission is frozen separately from compatibility. No conflict priority is
introduced by the construction. -/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch.GrammarRobust

open PermanssonLean PermanssonLean.RegimeSpecification

variable {S X A H Z : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MetricSpace Z]

abbrev PatchSelection (S X A : Type*) [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace A] :=
  List (RowPatch (JointState S X) A) × List (RowPatch (UpdateInput S X A) S)

noncomputable def overlapFamily (M : StrategicWorldModel S X A)
    (admitted : PatchSelection S X A → Prop) :
    InterventionFamily M (PatchSelection S X A) where
  targetOf _ := .jointStrategic
  admissible b g := admitted b ∧ g = (overlapModel M b.1 b.2).generator

noncomputable def overlapIntervention (M : StrategicWorldModel S X A)
    (admitted : PatchSelection S X A → Prop)
    (b : PatchSelection S X A) (hb : admitted b) :
    AdmissibleStrategicIntervention (overlapFamily M admitted) where
  intervention := ⟨b, (overlapModel M b.1 b.2).generator⟩
  accepted := ⟨hb, rfl⟩
  strategic := InterventionTarget.isStrategic_jointStrategic

theorem overlapIntervention_apply (M : StrategicWorldModel S X A)
    (admitted : PatchSelection S X A → Prop)
    (b : PatchSelection S X A) (hb : admitted b) :
    (overlapIntervention M admitted b hb).intervention.apply = overlapModel M b.1 b.2 := rfl

theorem overlapIntervention_effect_eq (M : StrategicWorldModel S X A)
    (admitted : PatchSelection S X A → Prop)
    (b c : PatchSelection S X A) (hb : admitted b) (hc : admitted c)
    (ha : ∀ p ∈ b.1, ∀ q ∈ b.1, p.Compatible q)
    (hu : ∀ p ∈ b.2, ∀ q ∈ b.2, p.Compatible q)
    (hac : ∀ p, p ∈ b.1 ↔ p ∈ c.1) (huc : ∀ p, p ∈ b.2 ↔ p ∈ c.2)
    (ψ : RegimePropertyMap (JointState S X) Z) (y : JointState S X) :
    constitutiveEffect M ψ (overlapIntervention M admitted b hb) y =
      constitutiveEffect M ψ (overlapIntervention M admitted c hc) y := by
  unfold constitutiveEffect intervenedPropertyValue
  rw [overlapIntervention_apply, overlapIntervention_apply,
    overlapModel_eq_of_membership M b.1 c.1 b.2 c.2 ha hu hac huc]

theorem overlapIntervention_margin_eq (M : StrategicWorldModel S X A)
    (admitted : PatchSelection S X A → Prop)
    (b c : PatchSelection S X A) (hb : admitted b) (hc : admitted c)
    (ha : ∀ p ∈ b.1, ∀ q ∈ b.1, p.Compatible q)
    (hu : ∀ p ∈ b.2, ∀ q ∈ b.2, p.Compatible q)
    (hac : ∀ p, p ∈ b.1 ↔ p ∈ c.1) (huc : ∀ p, p ∈ b.2 ↔ p ∈ c.2)
    (spec : RegimeSpecification (JointState S X) H)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) :
    constitutiveMargin M spec (overlapFamily M admitted) ψ B₁
        (overlapIntervention M admitted b hb) =
      constitutiveMargin M spec (overlapFamily M admitted) ψ B₁
        (overlapIntervention M admitted c hc) := by
  unfold constitutiveMargin
  apply congrArg sInf
  apply Set.image_congr
  intro y _
  exact overlapIntervention_effect_eq M admitted b c hb hc ha hu hac huc ψ y

end PermanssonResearch.GrammarRobust
