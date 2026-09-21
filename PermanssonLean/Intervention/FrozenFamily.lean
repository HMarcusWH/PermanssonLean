import PermanssonLean.Intervention.Apply

namespace PermanssonLean

universe uS uX uA uK uL

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- A concrete, predeclared family of admissible strategic interventions,
indexed by frozen labels.  This sits on top of `InterventionFamily`, which
stores the grammar and admissibility predicate rather than a chosen family of
intervention instances. -/
structure FrozenStrategicInterventionFamily
    {M : StrategicWorldModel S X A}
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (Label : Type uL) where
  intervention : Label → AdmissibleStrategicIntervention F
  label_nonempty : Nonempty Label

/-- Cross-model matching of two frozen families.  The label equivalence is
fixed ex ante and must preserve the declared intervention target. -/
structure FrozenFamilyMatching
    {M₁ M₂ : StrategicWorldModel S X A}
    {Component₁ : Type uK} {Component₂ : Type uK}
    {Label₁ : Type uL} {Label₂ : Type uL}
    (F₁ : InterventionFamily M₁ Component₁)
    (F₂ : InterventionFamily M₂ Component₂)
    (J₁ : FrozenStrategicInterventionFamily F₁ Label₁)
    (J₂ : FrozenStrategicInterventionFamily F₂ Label₂) where
  labelEquiv : Label₁ ≃ Label₂
  target_eq :
    ∀ l : Label₁,
      F₁.targetOf (J₁.intervention l).intervention.component =
        F₂.targetOf (J₂.intervention (labelEquiv l)).intervention.component

end PermanssonLean
