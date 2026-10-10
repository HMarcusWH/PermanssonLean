import PermanssonResearch.GrammarRobust.Minimality

/-!
# Lane B — preservation of minimality under a genuine order isomorphism

Matching effects is insufficient.  The matching of admissible blocks must
preserve AND REFLECT proper-subblock inclusion.  This generic theorem is
the finite-poset portion of the grammar-robustness contract; physical atom
and path-law matching are proved separately in refinement transport.
-/

namespace PermanssonResearch
namespace GrammarRobust

universe uI uJ uC uD

theorem minimalAllowed_iff_of_blockOrderEquiv
    {IA : Type uI} {IU : Type uJ} {C : Type uC} {D : Type uD}
    [Fintype IA] [Fintype IU] [Fintype C] [Fintype D]
    (Γ₁ : PartitionGrammar IA IU C)
    (Γ₂ : PartitionGrammar IA IU D)
    (P₁ : Finset C → Prop) (P₂ : Finset D → Prop)
    (φ : Finset C ≃ Finset D)
    (hallowed : ∀ E : Finset C,
      Γ₁.allowed E ↔ Γ₂.allowed (φ E))
    (hproperty : ∀ E : Finset C,
      P₁ E ↔ P₂ (φ E))
    (horder : ∀ E F : Finset C,
      E ⊂ F ↔ φ E ⊂ φ F)
    (E : Finset C) :
    IsMinimalAllowed Γ₁ P₁ E ↔
      IsMinimalAllowed Γ₂ P₂ (φ E) := by
  constructor
  · rintro ⟨hallow, hpositive, hminimal⟩
    refine ⟨(hallowed E).1 hallow, (hproperty E).1 hpositive, ?_⟩
    intro F hFallow hFproper hFpositive
    let G : Finset C := φ.symm F
    have hGallow : Γ₁.allowed G := by
      apply (hallowed G).2
      simpa [G] using hFallow
    have hGproper : G ⊂ E := by
      apply (horder G E).2
      simpa [G] using hFproper
    have hGpositive : P₁ G := by
      apply (hproperty G).2
      simpa [G] using hFpositive
    exact hminimal G hGallow hGproper hGpositive
  · rintro ⟨hallow, hpositive, hminimal⟩
    refine ⟨(hallowed E).2 hallow, (hproperty E).2 hpositive, ?_⟩
    intro F hFallow hFproper hFpositive
    apply hminimal (φ F)
    · exact (hallowed F).1 hFallow
    · exact (horder F E).1 hFproper
    · exact (hproperty F).1 hFpositive

end GrammarRobust
end PermanssonResearch
