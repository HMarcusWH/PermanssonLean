import PermanssonResearch.GrammarRobust.RefinementTransport
import PermanssonResearch.GrammarRobust.BlockConstitution

/-!
# Lane B — constitutive-effect transport across *non-bijective* coarsening

The model equality comes from the atom partition refinement theorem.
No equality of affected kernels or constitutive effects is assumed.
The same frozen property, comparison set and full canonical path laws are used.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust

universe uS uX uA uI uJ uF uC uH uZ

noncomputable def Coarsening.liftAllowed
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [Fintype Fine] [Fintype Coarse]
    [DecidableEq Coarse]
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse)
    (D : AllowedBlock coarse) : AllowedBlock fine :=
  ⟨ρ.lift D.components, ρ.respects_allowed D.components D.accepted⟩

theorem Coarsening.admitted_apply_lift_eq
    {S : Type uS} {X : Type uX} {A : Type uA}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [Fintype Fine] [Fintype Coarse]
    [LinearOrder IA] [LinearOrder IU] [DecidableEq Coarse]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse)
    (D : AllowedBlock coarse) :
    (admittedBlockIntervention M bank fine (ρ.liftAllowed D)).intervention.apply =
    (admittedBlockIntervention M bank coarse D).intervention.apply := by
  rw [admittedBlockIntervention_apply, admittedBlockIntervention_apply]
  exact ρ.blockModel_lift_eq M bank D.components

theorem Coarsening.blockEffect_lift_eq
    {S : Type uS} {X : Type uX} {A : Type uA} {Z : Type uZ}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    [MetricSpace Z]
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [Fintype Fine] [Fintype Coarse]
    [LinearOrder IA] [LinearOrder IU] [DecidableEq Coarse]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse)
    (D : AllowedBlock coarse)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) :
    blockEffect M bank fine (ρ.liftAllowed D) ψ y =
      blockEffect M bank coarse D ψ y := by
  unfold blockEffect
    PermanssonLean.RegimeSpecification.constitutiveEffect
    PermanssonLean.RegimeSpecification.intervenedPropertyValue
  rw [ρ.admitted_apply_lift_eq M bank D]

theorem Coarsening.blockMargin_lift_eq
    {S : Type uS} {X : Type uX} {A : Type uA}
    {H : Type uH} {Z : Type uZ}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace H] [TopologicalSpace S] [TopologicalSpace X]
    [MetricSpace Z]
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [Fintype Fine] [Fintype Coarse]
    [LinearOrder IA] [LinearOrder IU] [DecidableEq Coarse]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse)
    (D : AllowedBlock coarse)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec) :
    blockMargin M bank fine (ρ.liftAllowed D) spec ψ B₁ =
      blockMargin M bank coarse D spec ψ B₁ := by
  unfold blockMargin PermanssonLean.RegimeSpecification.constitutiveMargin
  apply congrArg sInf
  apply Set.image_congr
  intro y hy
  exact ρ.blockEffect_lift_eq M bank D ψ y

end GrammarRobust
end PermanssonResearch
