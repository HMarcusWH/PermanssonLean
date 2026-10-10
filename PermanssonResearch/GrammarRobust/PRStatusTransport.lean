import PermanssonResearch.GrammarRobust.ConstitutionTransport
import PermanssonLean.Regime.UniformPermansson

/-!
# Lane B — full typed relative PR status under genuine coarsening

The baseline, exact GR condition, fixed regime property and comparison set
are identical on both sides. Each matched block has equal *constructed*
canonical α/P/U model. This transfers original pointwise strategic
constitution and its quantitative uniform strengthening, not merely a
numerical surrogate.
-/

open MeasureTheory ProbabilityTheory PermanssonLean.RegimeSpecification

namespace PermanssonResearch
namespace GrammarRobust

universe uS uX uA uI uJ uF uC uH uZ

theorem Coarsening.relativePR_lift_iff
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
    (m : Measure (PermanssonLean.JointState S X))
    (ψ : PermanssonLean.RegimePropertyMap
      (PermanssonLean.JointState S X) Z)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec) :
    PermanssonLean.RegimeSpecification.IsGeneralizedPermanssonRegimeRelative
      M spec m (blockFamily M bank fine) ψ B₁
      (admittedBlockIntervention M bank fine (ρ.liftAllowed D)) ↔
    PermanssonLean.RegimeSpecification.IsGeneralizedPermanssonRegimeRelative
      M spec m (blockFamily M bank coarse) ψ B₁
      (admittedBlockIntervention M bank coarse D) := by
  change
    (IsExactGeneratedRegime M spec m ∧
      ∀ y ∈ B₁.states,
        baselinePropertyValue ψ M y ≠
          intervenedPropertyValue ψ
            (admittedBlockIntervention M bank fine
              (ρ.liftAllowed D)).intervention y) ↔
    (IsExactGeneratedRegime M spec m ∧
      ∀ y ∈ B₁.states,
        baselinePropertyValue ψ M y ≠
          intervenedPropertyValue ψ
            (admittedBlockIntervention M bank coarse D).intervention y)
  have hmodel := ρ.admitted_apply_lift_eq M bank D
  simp only [PermanssonLean.RegimeSpecification.intervenedPropertyValue,
    hmodel]

theorem Coarsening.uniformRelativePR_lift_iff
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
    (m : Measure (PermanssonLean.JointState S X))
    (ψ : PermanssonLean.RegimePropertyMap
      (PermanssonLean.JointState S X) Z)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec) :
    PermanssonLean.RegimeSpecification.IsUniformGeneralizedPermanssonRegimeRelative
      M spec m (blockFamily M bank fine) ψ B₁
      (admittedBlockIntervention M bank fine (ρ.liftAllowed D)) ↔
    PermanssonLean.RegimeSpecification.IsUniformGeneralizedPermanssonRegimeRelative
      M spec m (blockFamily M bank coarse) ψ B₁
      (admittedBlockIntervention M bank coarse D) := by
  change
    (IsExactGeneratedRegime M spec m ∧
      IsUniformlyStrategicallyConstitutive M spec
        (blockFamily M bank fine) ψ B₁
        (admittedBlockIntervention M bank fine (ρ.liftAllowed D))) ↔
    (IsExactGeneratedRegime M spec m ∧
      IsUniformlyStrategicallyConstitutive M spec
        (blockFamily M bank coarse) ψ B₁
        (admittedBlockIntervention M bank coarse D))
  apply and_congr Iff.rfl
  calc
    IsUniformlyStrategicallyConstitutive M spec
        (blockFamily M bank fine) ψ B₁
        (admittedBlockIntervention M bank fine (ρ.liftAllowed D)) ↔
      0 < blockMargin M bank fine (ρ.liftAllowed D) spec ψ B₁ :=
        uniformlyConstitutive_iff_margin_pos
          M spec (blockFamily M bank fine) ψ B₁
          (admittedBlockIntervention M bank fine (ρ.liftAllowed D))
    _ ↔ 0 < blockMargin M bank coarse D spec ψ B₁ := by
      rw [ρ.blockMargin_lift_eq M bank D spec ψ B₁]
    _ ↔ IsUniformlyStrategicallyConstitutive M spec
        (blockFamily M bank coarse) ψ B₁
        (admittedBlockIntervention M bank coarse D) :=
      (uniformlyConstitutive_iff_margin_pos
        M spec (blockFamily M bank coarse) ψ B₁
        (admittedBlockIntervention M bank coarse D)).symm

end GrammarRobust
end PermanssonResearch
