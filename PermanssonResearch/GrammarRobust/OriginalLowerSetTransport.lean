import PermanssonResearch.GrammarRobust.LowerSetTransport
import PermanssonResearch.GrammarRobust.ImageMinimality

/-! B-LOCAL-ORDER instantiated with actual original constitutive margins.
The match is proved from the physical atom expansion theorem and canonical
models. Coverage of all admitted strict lower blocks remains an explicit gate. -/

open MeasureTheory

namespace PermanssonResearch.GrammarRobust

variable {S X A H Z IA IU Fine Coarse : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [TopologicalSpace S] [TopologicalSpace X] [MetricSpace Z]
variable [Fintype IA] [Fintype IU] [DecidableEq IA] [DecidableEq IU]
variable [Fintype Fine] [Fintype Coarse]
variable [LinearOrder IA] [LinearOrder IU] [DecidableEq Coarse]

theorem Coarsening.original_margin_minimal_iff_of_lower_coverage
    (M : PermanssonLean.StrategicWorldModel S X A) (bank : AtomicBank M IA IU)
    {fine : PartitionGrammar IA IU Fine} {coarse : PartitionGrammar IA IU Coarse}
    (ρ : Coarsening fine coarse)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (ψ : PermanssonLean.RegimePropertyMap (PermanssonLean.JointState S X) Z)
    (B₁ : PermanssonLean.RegimeSpecification.ConstitutiveComparisonSet M spec)
    (D : Finset Coarse) (hD : coarse.allowed D)
    (hcover : ∀ E, fine.allowed E → E ⊂ ρ.lift D →
      ∃ C, coarse.allowed C ∧ C ⊂ D ∧ ρ.lift C = E) :
    IsMinimalAllowed coarse
      (fun C => ∃ hC, 0 < blockMargin M bank coarse ⟨C, hC⟩ spec ψ B₁) D ↔
    IsMinimalAllowed fine
      (fun E => ∃ hE, 0 < blockMargin M bank fine ⟨E, hE⟩ spec ψ B₁) (ρ.lift D) := by
  have hmatch (C : Finset Coarse) (hC : coarse.allowed C) :
      (∃ h, 0 < blockMargin M bank coarse ⟨C, h⟩ spec ψ B₁) ↔
      (∃ h, 0 < blockMargin M bank fine ⟨ρ.lift C, h⟩ spec ψ B₁) := by
    have heq := ρ.blockMargin_lift_eq M bank ⟨C, hC⟩ spec ψ B₁
    constructor
    · rintro ⟨_, hpos⟩
      exact ⟨ρ.respects_allowed C hC, heq.symm ▸ hpos⟩
    · rintro ⟨_, hpos⟩
      exact ⟨hC, heq ▸ hpos⟩
  constructor
  · rintro ⟨hD, hpos, hmin⟩
    refine ⟨ρ.respects_allowed D hD, (hmatch D hD).mp hpos, ?_⟩
    intro E hE hED hpositive
    obtain ⟨C, hC, hCD, hCE⟩ := hcover E hE hED
    apply hmin C hC hCD
    apply (hmatch C hC).mpr
    simpa only [hCE] using hpositive
  · rintro ⟨_, hpos, hmin⟩
    refine ⟨hD, (hmatch D hD).mpr hpos, ?_⟩
    intro C hC hCD hpositive
    exact hmin (ρ.lift C) (ρ.respects_allowed C hC)
      ((ρ.lift_ssubset_iff C D).mpr hCD) ((hmatch C hC).mp hpositive)

end PermanssonResearch.GrammarRobust
