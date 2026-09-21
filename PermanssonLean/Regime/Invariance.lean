import PermanssonLean.Regime.Specification
import PermanssonLean.StrategicWorld.InducedKernel

open MeasureTheory

namespace PermanssonLean

universe uS uX uA uH

variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

namespace RegimeSpecification

/-- Exact one-step invariance of the frozen regime region B under the
canonical induced strategic-world kernel. -/
def IsExactlyInvariant
    (M : StrategicWorldModel S X A)
    (Σ : RegimeSpecification (JointState S X) H) : Prop :=
  ∀ y ∈ Σ.region, M.inducedKernel y Σ.region = 1

theorem exactInvariant_at
    (M : StrategicWorldModel S X A)
    (Σ : RegimeSpecification (JointState S X) H)
    (h : IsExactlyInvariant M Σ)
    {y : JointState S X} (hy : y ∈ Σ.region) :
    M.inducedKernel y Σ.region = 1 :=
  h y hy

end RegimeSpecification

end PermanssonLean
