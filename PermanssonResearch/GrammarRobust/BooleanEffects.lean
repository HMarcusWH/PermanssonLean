import PermanssonResearch.GrammarRobust.BooleanOneStepEvents
import PermanssonResearch.GrammarRobust.MarginFromEffects
import Mathlib.Tactic

/-!
# Lane B — checked constitutive effects for OR, AND and XOR path properties

All effects are distances between the *original path-law evaluations* of
actual alpha/P/U intervention models. They demonstrate:
- joint-only constitution (OR);
- redundant support and incomparable candidates (AND);
- violation of upward monotonicity (XOR).

The accompanying uniform margins are derived by the same original
sInf constitutive-margin definition, not a surrogate objective.
-/

namespace PermanssonResearch
namespace GrammarRobust
namespace BooleanEffects

open PermanssonLean PermanssonLean.RegimeSpecification
open BooleanModel BooleanBaseline BooleanDynamics BooleanPersistence
open BooleanOneStepEvents

theorem or_action_zero (y : Y) :
    blockEffect baseline bank fine actionBlock (propertyAtOne orP) y = 0 := by
  obtain ⟨hb,ha,hu,hj⟩ := or_pathlaw_table y
  unfold blockEffect constitutiveEffect
  rw [hb,ha]
  simp

theorem or_update_zero (y : Y) :
    blockEffect baseline bank fine updateBlock (propertyAtOne orP) y = 0 := by
  obtain ⟨hb,ha,hu,hj⟩ := or_pathlaw_table y
  unfold blockEffect constitutiveEffect
  rw [hb,hu]
  simp

theorem or_joint_one (y : Y) :
    blockEffect baseline bank fine jointBlock (propertyAtOne orP) y = 1 := by
  obtain ⟨hb,ha,hu,hj⟩ := or_pathlaw_table y
  unfold blockEffect constitutiveEffect
  rw [hb,hj]
  norm_num

theorem and_action_one (y : Y) :
    blockEffect baseline bank fine actionBlock (propertyAtOne andP) y = 1 := by
  obtain ⟨hb,ha,hu,hj⟩ := and_pathlaw_table y
  unfold blockEffect constitutiveEffect
  rw [hb,ha]
  norm_num

theorem and_update_one (y : Y) :
    blockEffect baseline bank fine updateBlock (propertyAtOne andP) y = 1 := by
  obtain ⟨hb,ha,hu,hj⟩ := and_pathlaw_table y
  unfold blockEffect constitutiveEffect
  rw [hb,hu]
  norm_num

theorem and_joint_one (y : Y) :
    blockEffect baseline bank fine jointBlock (propertyAtOne andP) y = 1 := by
  obtain ⟨hb,ha,hu,hj⟩ := and_pathlaw_table y
  unfold blockEffect constitutiveEffect
  rw [hb,hj]
  norm_num

theorem xor_action_one (y : Y) :
    blockEffect baseline bank fine actionBlock (propertyAtOne xorP) y = 1 := by
  obtain ⟨hb,ha,hu,hj⟩ := xor_pathlaw_table y
  unfold blockEffect constitutiveEffect
  rw [hb,ha]
  norm_num

theorem xor_update_one (y : Y) :
    blockEffect baseline bank fine updateBlock (propertyAtOne xorP) y = 1 := by
  obtain ⟨hb,ha,hu,hj⟩ := xor_pathlaw_table y
  unfold blockEffect constitutiveEffect
  rw [hb,hu]
  norm_num

theorem xor_joint_zero (y : Y) :
    blockEffect baseline bank fine jointBlock (propertyAtOne xorP) y = 0 := by
  obtain ⟨hb,ha,hu,hj⟩ := xor_pathlaw_table y
  unfold blockEffect constitutiveEffect
  rw [hb,hj]
  simp

theorem or_singleton_margins_zero :
    blockMargin baseline bank fine actionBlock spec
      (propertyAtOne orP) comparison = 0 ∧
    blockMargin baseline bank fine updateBlock spec
      (propertyAtOne orP) comparison = 0 := by
  constructor
  · apply blockMargin_eq_of_constant_effect
    intro y hy
    exact or_action_zero y
  · apply blockMargin_eq_of_constant_effect
    intro y hy
    exact or_update_zero y

theorem or_joint_margin_one :
    blockMargin baseline bank fine jointBlock spec
      (propertyAtOne orP) comparison = 1 := by
  apply blockMargin_eq_of_constant_effect
  intro y hy
  exact or_joint_one y

theorem and_singleton_margins_one :
    blockMargin baseline bank fine actionBlock spec
      (propertyAtOne andP) comparison = 1 ∧
    blockMargin baseline bank fine updateBlock spec
      (propertyAtOne andP) comparison = 1 := by
  constructor
  · apply blockMargin_eq_of_constant_effect
    intro y hy
    exact and_action_one y
  · apply blockMargin_eq_of_constant_effect
    intro y hy
    exact and_update_one y

theorem xor_nonmonotone_margins :
    blockMargin baseline bank fine actionBlock spec
      (propertyAtOne xorP) comparison = 1 ∧
    blockMargin baseline bank fine jointBlock spec
      (propertyAtOne xorP) comparison = 0 := by
  constructor
  · apply blockMargin_eq_of_constant_effect
    intro y hy
    exact xor_action_one y
  · apply blockMargin_eq_of_constant_effect
    intro y hy
    exact xor_joint_zero y

end BooleanEffects
end GrammarRobust
end PermanssonResearch
