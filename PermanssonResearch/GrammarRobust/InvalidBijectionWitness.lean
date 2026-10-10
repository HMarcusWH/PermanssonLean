import PermanssonResearch.GrammarRobust.BooleanMinimalityCases
import Mathlib.Tactic

/-!
# Lane B B5 — why matching effect values under an arbitrary block-label
# bijection does NOT preserve minimality

The AND property is an actual canonical path-law property. Action singleton
and action+update joint have the *same* original constitutive margin, but the
singleton is minimal and the joint block is not. A bijection swapping these
two block labels matches their effects and breaks proper-subblock order.
Such an arbitrary label permutation is not a valid grammar equivalence.
-/

namespace PermanssonResearch
namespace GrammarRobust
namespace InvalidBijectionWitness

open BooleanModel BooleanBaseline BooleanDynamics
open BooleanPersistence BooleanOneStepEvents BooleanEffects
open BooleanMinimalityCases

def actionLabel : Finset (Fin 2) := {0}
def compoundLabel : Finset (Fin 2) := {0,1}

/-- An actual bijection of the four *block labels*, not a componentwise
bijection of the two underlying strategic components. -/
def invalidBlockSwap : Finset (Fin 2) ≃ Finset (Fin 2) :=
  Equiv.swap actionLabel compoundLabel

theorem invalid_swap_action :
    invalidBlockSwap actionLabel = compoundLabel := by
  simp [invalidBlockSwap]

theorem invalid_swap_joint :
    invalidBlockSwap compoundLabel = actionLabel := by
  simp [invalidBlockSwap]

theorem matched_AND_margins :
    blockMargin baseline bank fine (fineBlock actionLabel)
      spec (propertyAtOne andP) comparison =
    blockMargin baseline bank fine (fineBlock compoundLabel)
      spec (propertyAtOne andP) comparison := by
  have ha := and_singleton_margins_one.1
  have hj : blockMargin baseline bank fine jointBlock spec
      (propertyAtOne andP) comparison = 1 := by
    apply blockMargin_eq_of_constant_effect
    intro y _
    exact and_joint_one y
  change blockMargin baseline bank fine actionBlock spec
    (propertyAtOne andP) comparison =
    blockMargin baseline bank fine jointBlock spec
    (propertyAtOne andP) comparison
  rw [ha, hj]

/-- B5: arbitrary block-label matching can preserve the margin for a
matched intervention while reversing its minimality status. -/
theorem equal_margin_but_invalid_minimality :
    andPos actionLabel ∧
    blockMargin baseline bank fine (fineBlock actionLabel)
      spec (propertyAtOne andP) comparison =
    blockMargin baseline bank fine (fineBlock (invalidBlockSwap actionLabel))
      spec (propertyAtOne andP) comparison ∧
    IsMinimalAllowed fine andPos actionLabel ∧
    ¬ IsMinimalAllowed fine andPos (invalidBlockSwap actionLabel) := by
  rw [invalid_swap_action]
  exact ⟨andPos_action, matched_AND_margins,
    and_action_minimal, and_joint_not_minimal⟩

/-- B5 strengthened: the invalid arbitrary block-label bijection preserves
the *entire* original AND constitutive-margin profile on all four
admissible fine blocks. It still fails to preserve minimality because
it is not an order isomorphism. -/
theorem AND_margin_invariant_under_invalid_swap
    (D : Finset (Fin 2)) :
    blockMargin baseline bank fine (fineBlock D)
      spec (propertyAtOne andP) comparison =
    blockMargin baseline bank fine (fineBlock (invalidBlockSwap D))
      spec (propertyAtOne andP) comparison := by
  classical
  by_cases ha : D = actionLabel
  · subst D
    rw [invalid_swap_action]
    exact matched_AND_margins
  by_cases hj : D = compoundLabel
  · subst D
    rw [invalid_swap_joint]
    exact matched_AND_margins.symm
  have hfixed : invalidBlockSwap D = D := by
    exact Equiv.swap_apply_of_ne_of_ne ha hj
  rw [hfixed]

theorem invalid_swap_does_not_preserve_proper_inclusion :
    ¬ ∀ D E : Finset (Fin 2),
       D ⊂ E ↔ invalidBlockSwap D ⊂ invalidBlockSwap E := by
  intro h
  have hs : actionLabel ⊂ compoundLabel := by
    decide
  have hf := (h actionLabel compoundLabel).mp hs
  rw [invalid_swap_action, invalid_swap_joint] at hf
  exact (Finset.ssubset_irrefl actionLabel) (hf.trans hs)

end InvalidBijectionWitness
end GrammarRobust
end PermanssonResearch
