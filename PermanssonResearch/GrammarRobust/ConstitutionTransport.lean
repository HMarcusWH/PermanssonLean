import PermanssonResearch.GrammarRobust.EffectTransport
import PermanssonResearch.GrammarRobust.BlockConstitution

/-!
# Lane B — classification preservation under genuine nonbijective coarsening

This is the *original* uniform constitutive-margin criterion, evaluated on
the same baseline Exact GR and frozen comparison set. The actual fine-lifted
and coarse interventions produce equal canonical path laws by construction;
we do not assume their effect equality as an axiom.
-/

open MeasureTheory
namespace PermanssonResearch
namespace GrammarRobust

universe uS uX uA uI uJ uF uC uH uZ

theorem Coarsening.uniformBlock_lift_iff
    {S : Type uS} {X : Type uX} {A : Type uA}
    {H : Type uH} {Z : Type uZ}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace H] [TopologicalSpace S] [TopologicalSpace X]
    [MetricSpace Z]
    {IA : Type uI} {IU : Type uJ}
    {Fine : Type uF} {Coarse : Type uC}
    [Fintype IA] [Fintype IU] [DecidableEq IA] [DecidableEq IU]
    [Fintype Fine] [Fintype Coarse]
    [LinearOrder IA] [LinearOrder IU] [DecidableEq Coarse]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    {fine : PartitionGrammar IA IU Fine}
    {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse)
    (D : AllowedBlock coarse)
    (spec : PermanssonLean.RegimeSpecification
      (PermanssonLean.JointState S X) H)
    (ψ : PermanssonLean.RegimePropertyMap
      (PermanssonLean.JointState S X) Z)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec) :
    IsUniformBlock M bank fine (ρ.liftAllowed D) spec ψ B₁ ↔
    IsUniformBlock M bank coarse D spec ψ B₁ := by
  change
    0 < blockMargin M bank fine (ρ.liftAllowed D) spec ψ B₁ ↔
      0 < blockMargin M bank coarse D spec ψ B₁
  rw [ρ.blockMargin_lift_eq M bank D spec ψ B₁]

end GrammarRobust
end PermanssonResearch
