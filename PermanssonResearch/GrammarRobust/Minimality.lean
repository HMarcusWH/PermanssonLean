import PermanssonResearch.GrammarRobust.BlockConstitution
import Mathlib.Tactic

/-!
# Lane B — existence of minimal constitutive blocks in a finite grammar

The allowed-block predicate is NOT downward-closed.  A minimal positive
block has no strictly smaller *allowed* positive subblock; several incomparable
minimal blocks can exist.  The proof uses least cardinality, not a monotonicity
assumption.
-/

namespace PermanssonResearch
namespace GrammarRobust

universe uI uJ uC

/-- Minimality inside the frozen admitted block poset. -/
def IsMinimalAllowed
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    (Γ : PartitionGrammar IA IU C)
    (P : Finset C → Prop) (D : Finset C) : Prop :=
  Γ.allowed D ∧ P D ∧
    ∀ E : Finset C, Γ.allowed E → E ⊂ D → ¬ P E

/-- An allowed positive finite block contains an allowed positive block of
least cardinality.  This does not choose a unique physical or semantic cause. -/
theorem exists_minimal_allowed_subblock
    {IA : Type uI} {IU : Type uJ} {C : Type uC}
    [Fintype IA] [Fintype IU] [Fintype C]
    (Γ : PartitionGrammar IA IU C)
    (P : Finset C → Prop)
    (D : Finset C) (hD : Γ.allowed D) (hP : P D) :
    ∃ E : Finset C, E ⊆ D ∧ IsMinimalAllowed Γ P E := by
  classical
  let Q (n : ℕ) : Prop :=
    ∃ E : Finset C, E ⊆ D ∧ Γ.allowed E ∧ P E ∧ E.card = n
  have hex : ∃ n : ℕ, Q n := by
    refine ⟨D.card, D, Finset.Subset.refl D, hD, hP, rfl⟩
  let n := Nat.find hex
  obtain ⟨E, hED, hallow, hpositive, hcard⟩ := Nat.find_spec hex
  refine ⟨E, hED, hallow, hpositive, ?_⟩
  intro F hFallow hFproper hFpositive
  have hFsub : F ⊆ D := (Finset.ssubset_iff_subset_ne.mp hFproper).1.trans hED
  have hFsmall : F.card < n := by
    exact (Finset.card_lt_card hFproper).trans_eq hcard
  have hFmin : n ≤ F.card :=
    Nat.find_min' hex ⟨F, hFsub, hFallow, hFpositive, rfl⟩
  omega

end GrammarRobust
end PermanssonResearch
