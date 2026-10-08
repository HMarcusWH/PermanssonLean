import PermanssonLean.Regime.Constitution
import PermanssonLean.Probability.FinitePrefixTV

/-!
# Research-to-core compatibility smoke test

The import checks below establish that research modules can depend on the
already-formalized GR/PR and finite-prefix TV interfaces. The small theorem merely
re-exports an already-proved typed world-preservation fact; it is not a new
mathematical claim or a CQ-1 result.
-/

namespace PermanssonResearch

open PermanssonLean

#check PermanssonLean.StrategicWorldModel
#check PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet
#check PermanssonLean.RegimeSpecification.IsStrategicallyConstitutive
#check PermanssonLean.ProbabilitySupport.finitePrefix_eventTotalVariation_le_geometric

universe uS uX uA uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- Compatibility witness only: a typed strategic intervention leaves the
existing world-transition primitive unchanged, by the existing core theorem. -/
theorem typedStrategicIntervention_world_eq
    (M : StrategicWorldModel S X A)
    {Component : Type uK}
    {F : InterventionFamily M Component}
    (J : AdmissibleStrategicIntervention F) :
    J.intervention.apply.world = M.world :=
  J.world_eq

end PermanssonResearch
