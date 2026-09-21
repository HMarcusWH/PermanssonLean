import PermanssonLean.Regime.Occupation
import PermanssonLean.Intervention.Apply

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uZ

/-- A regime-property map evaluates an entire path probability law.

No measurability assumption is imposed here: the basic constitution criterion
is pointwise and only requires comparing the resulting property values.
-/
abbrev RegimePropertyMap
    (Y : Type uS) [MeasurableSpace Y]
    (Z : Type uZ) :=
  ProbabilityMeasure (ℕ → Y) → Z

variable {S : Type uS} {X : Type uX} {A : Type uA} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

namespace RegimeSpecification

/-- Property value of the baseline point-initialized path law. -/
noncomputable def baselinePropertyValue
    (ψ : RegimePropertyMap (JointState S X) Z)
    (M : StrategicWorldModel S X A)
    (y : JointState S X) : Z :=
  ψ (pathProbability M (diracProba y))

/-- Property value of the point-initialized path law after a typed intervention. -/
noncomputable def intervenedPropertyValue
    {M : StrategicWorldModel S X A}
    {Component : Type*}
    {F : InterventionFamily M Component}
    (ψ : RegimePropertyMap (JointState S X) Z)
    (J : TypedIntervention F)
    (y : JointState S X) : Z :=
  ψ (pathProbability J.apply (diracProba y))

end RegimeSpecification

end PermanssonLean
