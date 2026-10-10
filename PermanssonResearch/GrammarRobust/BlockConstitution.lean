import PermanssonResearch.GrammarRobust.OriginalInterventionBridge
import PermanssonLean.Regime.Perturbation

/-!
# Lane B — original, path-law-based constitutive quantities

No second scientific definition of constitution is introduced.  The
effect/margin for a block are exactly the original v0.1.8 quantities,
evaluated on a constructed admissible joint-strategic intervention.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust

universe uS uX uA uI uJ uC uH uZ

noncomputable def blockEffect
    {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH} {Z : Type uZ}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace H] [MetricSpace Z]
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (Γ : PartitionGrammar IA IU C)
    (D : AllowedBlock Γ)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (y : PermanssonLean.JointState S X) : ℝ :=
  PermanssonLean.RegimeSpecification.constitutiveEffect M ψ
    (admittedBlockIntervention M bank Γ D) y

noncomputable def blockMargin
    {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH} {Z : Type uZ}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace H] [MetricSpace Z]
    [TopologicalSpace S] [TopologicalSpace X]
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (Γ : PartitionGrammar IA IU C)
    (D : AllowedBlock Γ)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec) : ℝ :=
  PermanssonLean.RegimeSpecification.constitutiveMargin M spec
    (blockFamily M bank Γ) ψ B₁
    (admittedBlockIntervention M bank Γ D)

/-- Block uniform constitution is exactly the original positive margin test. -/
def IsUniformBlock
    {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH} {Z : Type uZ}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace H] [TopologicalSpace S] [TopologicalSpace X] [MetricSpace Z]
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU)
    (Γ : PartitionGrammar IA IU C)
    (D : AllowedBlock Γ)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec) : Prop :=
  0 < blockMargin M bank Γ D spec ψ B₁

theorem uniformBlock_iff_original_uniformConstitutive
    {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH} {Z : Type uZ}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace H] [TopologicalSpace S] [TopologicalSpace X] [MetricSpace Z]
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU) (Γ : PartitionGrammar IA IU C)
    (D : AllowedBlock Γ)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec) :
    IsUniformBlock M bank Γ D spec ψ B₁ ↔
      PermanssonLean.RegimeSpecification.IsUniformlyStrategicallyConstitutive
        M spec (blockFamily M bank Γ) ψ B₁
        (admittedBlockIntervention M bank Γ D) := by
  exact (PermanssonLean.RegimeSpecification.uniformlyConstitutive_iff_margin_pos
    M spec (blockFamily M bank Γ) ψ B₁
    (admittedBlockIntervention M bank Γ D)).symm

end GrammarRobust
end PermanssonResearch
