import PermanssonLean.Intervention.Replacement

namespace PermanssonLean

universe uS uX uA uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- A frozen intervention family.

Each predeclared component has exactly one target. Admissibility is also frozen
at the family boundary, allowing application-specific feasibility restrictions
without weakening the target typing enforced by Lean.
-/
structure InterventionFamily
    (M : StrategicWorldModel S X A)
    (Component : Type uK) where
  targetOf : Component → InterventionTarget
  admissible :
    (k : Component) →
      InterventionReplacement S X A (targetOf k) →
      Prop

/-- A target-correct intervention on one predeclared component. -/
structure TypedIntervention
    {M : StrategicWorldModel S X A}
    {Component : Type uK}
    (F : InterventionFamily M Component) where
  component : Component
  replacement :
    InterventionReplacement S X A (F.targetOf component)

namespace TypedIntervention

/-- The frozen family-level feasibility/admissibility predicate. -/
def IsAdmissible
    {M : StrategicWorldModel S X A}
    {Component : Type uK}
    {F : InterventionFamily M Component}
    (J : TypedIntervention F) : Prop :=
  F.admissible J.component J.replacement

/-- Whether the intervention targets the strategic generator rather than P. -/
def IsStrategic
    {M : StrategicWorldModel S X A}
    {Component : Type uK}
    {F : InterventionFamily M Component}
    (J : TypedIntervention F) : Prop :=
  (F.targetOf J.component).IsStrategic

end TypedIntervention

/-- Bundled certificate that a typed intervention belongs to the declared
admissible family. -/
structure AdmissibleIntervention
    {M : StrategicWorldModel S X A}
    {Component : Type uK}
    (F : InterventionFamily M Component) where
  intervention : TypedIntervention F
  accepted : intervention.IsAdmissible

/-- Admissible intervention restricted to strategic-generator targets.

This is the certificate later PR-constitution theorems should quantify over.
A structural world-transition intervention cannot inhabit this type.
-/
structure AdmissibleStrategicIntervention
    {M : StrategicWorldModel S X A}
    {Component : Type uK}
    (F : InterventionFamily M Component) where
  intervention : TypedIntervention F
  accepted : intervention.IsAdmissible
  strategic : intervention.IsStrategic

end PermanssonLean
