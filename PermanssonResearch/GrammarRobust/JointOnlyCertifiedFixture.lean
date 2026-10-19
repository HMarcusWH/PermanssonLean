import PermanssonResearch.GrammarRobust.BooleanMinimalityCases
import PermanssonResearch.GrammarRobust.BooleanEffects
import Mathlib.Tactic

/-!
# NEXT-06 / D-08 — a genuinely typed joint-only certified block

This reuses the existing frozen Boolean alpha/P/U process, its ORIGINAL
constitutive margin on the unchanged certified comparison set, and the
admissible-block grammar. It explicitly distinguishes the OR case, where
only the full joint block is positive, from the AND case, where both
singleton blocks have positive margins and the joint block is not minimal.

This is an acceptance witness for already proved source theorems, NOT a
new controlled-kernel generalization or a license to infer admissibility
for an arbitrary joint block.
-/

namespace PermanssonResearch.GrammarRobust.JointOnlyCertified

open PermanssonResearch.GrammarRobust
open PermanssonResearch.GrammarRobust.BooleanModel
open PermanssonResearch.GrammarRobust.BooleanEffects
open PermanssonResearch.GrammarRobust.BooleanMinimalityCases
open PermanssonResearch.GrammarRobust.BooleanOneStepEvents
open PermanssonLean
open PermanssonLean.RegimeSpecification

/-- The actual original full-comparison OR margin is one for the
joint-strategic block, but zero for either singleton and the empty block. -/
theorem original_or_joint_only :
    blockMargin baseline bank fine jointBlock spec
        (propertyAtOne orP) comparison = 1 ∧
    blockMargin baseline bank fine actionBlock spec
        (propertyAtOne orP) comparison = 0 ∧
    blockMargin baseline bank fine updateBlock spec
        (propertyAtOne orP) comparison = 0 ∧
    blockMargin baseline bank fine (fineBlock ∅) spec
        (propertyAtOne orP) comparison = 0 := by
  exact ⟨or_joint_margin_one, or_singleton_margins_zero.1,
    or_singleton_margins_zero.2, fine_empty_margin_zero _⟩

/-- Admission and minimality refer to the actual partition-grammar carrier,
not to an inferred downward-closed collection of raw labels. -/
theorem original_or_joint_is_minimal :
    IsMinimalAllowed fine orPos ({0,1} : Finset (Fin 2)) :=
  or_joint_minimal

/-- The OR-labelled joint-only block must not be mislabeled as an AND
singletons-positive result. The two original outcomes are different. -/
theorem original_and_has_two_distinct_minimal_singletons :
    IsMinimalAllowed fine andPos ({0} : Finset (Fin 2)) ∧
    IsMinimalAllowed fine andPos ({1} : Finset (Fin 2)) ∧
    ¬ IsMinimalAllowed fine andPos ({0,1} : Finset (Fin 2)) :=
  ⟨and_action_minimal, and_update_minimal, and_joint_not_minimal⟩

/-- A candidate claim that the admitted OR action-only block has a
positive original margin is demonstrably false in this concrete model. -/
theorem original_or_action_not_positive :
    ¬ (0 < blockMargin baseline bank fine actionBlock spec
      (propertyAtOne orP) comparison) := by
  rw [or_singleton_margins_zero.1]
  norm_num

end PermanssonResearch.GrammarRobust.JointOnlyCertified
