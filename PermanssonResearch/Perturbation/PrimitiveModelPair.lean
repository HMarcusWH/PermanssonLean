import PermanssonResearch.ConstitutiveQuasi.ComparisonTransport

/-!
# A2: paired typed models with distinct structural world primitives

Unlike the frozen CQ-1 `StrategicApproximationPair`, this comparison
permits `M.world ≠ approximate.world`. The difference is an error between
models, NOT an admissible strategic intervention within either model.

Both interventions are valid strategic replacements under their respective
frozen families. The comparison requires exactly the same named component
and the same target constructor: equal names without equal targets do not
constitute a matched protocol. All quantified primitive error assumptions
are supplied separately, including rows reached only after intervention.
-/

namespace PermanssonResearch
namespace Perturbation

universe uS uX uA uC

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- Typed original/approximate model pair with explicitly matched strategic
interventions and *no* forced equality of their world kernels. -/
structure PrimitiveModelPair
    (M : PermanssonLean.StrategicWorldModel S X A)
    {Component : Type uC}
    (F : PermanssonLean.InterventionFamily M Component)
    (J : PermanssonLean.AdmissibleStrategicIntervention F) where
  approximate : PermanssonLean.StrategicWorldModel S X A
  approximateFamily : PermanssonLean.InterventionFamily approximate Component
  approximateIntervention :
    PermanssonLean.AdmissibleStrategicIntervention approximateFamily
  component_eq :
    approximateIntervention.intervention.component = J.intervention.component
  target_eq :
    approximateFamily.targetOf approximateIntervention.intervention.component =
      F.targetOf J.intervention.component

/-- The original intervention leaves the original structural world primitive
unchanged. This is guaranteed by the original target-typed API. -/
theorem PrimitiveModelPair.original_world_fixed
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    (pair : PrimitiveModelPair M F J) :
    J.intervention.apply.world = M.world :=
  J.world_eq

/-- The matched approximate strategic intervention leaves the *approximate*
world primitive unchanged, which need not be equal to the original P. -/
theorem PrimitiveModelPair.approximate_world_fixed
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    (pair : PrimitiveModelPair M F J) :
    pair.approximateIntervention.intervention.apply.world =
      pair.approximate.world :=
  pair.approximateIntervention.world_eq

/-- Same original comparison set as the approximate model, under the
original source's explicit point-separation hypothesis. No kernel equality. -/
noncomputable def PrimitiveModelPair.comparisonSet
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    {H : Type*} [MeasurableSpace H]
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    (pair : PrimitiveModelPair M F J)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec) :
    PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet
      pair.approximate spec :=
  PermanssonResearch.ConstitutiveQuasi.transportComparisonSet
    M pair.approximate spec B₁

@[simp]
theorem PrimitiveModelPair.comparisonSet_states
    [MeasurableSpace.SeparatesPoints (PermanssonLean.JointState S X)]
    {H : Type*} [MeasurableSpace H]
    {M : PermanssonLean.StrategicWorldModel S X A}
    {Component : Type uC}
    {F : PermanssonLean.InterventionFamily M Component}
    {J : PermanssonLean.AdmissibleStrategicIntervention F}
    (pair : PrimitiveModelPair M F J)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec) :
    (pair.comparisonSet spec B₁).states = B₁.states :=
  rfl

end Perturbation
end PermanssonResearch
