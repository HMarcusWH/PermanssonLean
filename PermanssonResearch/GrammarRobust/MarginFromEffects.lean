import PermanssonResearch.GrammarRobust.BlockConstitution
import Mathlib.Tactic

/-!
# Lane B — exact uniform margins from a genuinely evaluated path-law effect

No independent surrogate for the original constitutive margin is introduced.
If the constructed original path-law effect equals r on the entire nonempty
comparison set, its original sInf-based uniform margin equals r.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace GrammarRobust

universe uS uX uA uI uJ uC uH uZ

theorem blockMargin_eq_of_constant_effect
    {S : Type uS} {X : Type uX} {A : Type uA}
    {H : Type uH} {Z : Type uZ}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace H] [TopologicalSpace S] [TopologicalSpace X]
    [MetricSpace Z]
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    [LinearOrder IA] [LinearOrder IU]
    (M : PermanssonLean.StrategicWorldModel S X A)
    (bank : AtomicBank M IA IU) (Γ : PartitionGrammar IA IU C)
    (D : AllowedBlock Γ)
    (spec : PermanssonLean.RegimeSpecification
      (PermanssonLean.JointState S X) H)
    (ψ : PermanssonLean.RegimePropertyMap
      (PermanssonLean.JointState S X) Z)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec)
    (r : ℝ)
    (heffect : ∀ y ∈ B₁.states, blockEffect M bank Γ D ψ y = r) :
    blockMargin M bank Γ D spec ψ B₁ = r := by
  unfold blockMargin PermanssonLean.RegimeSpecification.constitutiveMargin
  change sInf (blockEffect M bank Γ D ψ '' B₁.states) = r
  have hset : blockEffect M bank Γ D ψ '' B₁.states = {r} := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact heffect y hy
    · intro hz
      rcases B₁.states_nonempty M spec with ⟨y,hy⟩
      refine ⟨y,hy,?_⟩
      rw [heffect y hy]
      simpa using hz.symm
  rw [hset]
  simp

end GrammarRobust
end PermanssonResearch
