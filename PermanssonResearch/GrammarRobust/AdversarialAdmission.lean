import PermanssonResearch.GrammarRobust.BooleanEffects
import PermanssonResearch.GrammarRobust.TwoActionRows
import Mathlib.Tactic

/-!
# Lane B — B9/B11 adversarial construction and rejection

The disjoint atomic bank cannot admit two action atoms whose row masks
are both all of the input space. Separately, a finite frozen grammar can
reject the syntactically meaningful joint component block; there exists
no `AllowedBlock` certificate for it even though each singleton is allowed.
-/

namespace PermanssonResearch
namespace GrammarRobust
namespace AdversarialAdmission

open BooleanModel BooleanDynamics

/-- B9: two distinct full-overlap alpha atoms cannot inhabit AtomicBank. -/
theorem overlapping_action_rows_rejected :
    ¬ ∃ alt : AtomicBank baseline (Fin 2) (Fin 0),
        (alt.action (0 : Fin 2)).region = Set.univ ∧
        (alt.action (1 : Fin 2)).region = Set.univ := by
  rintro ⟨alt, h0, h1⟩
  have hd := alt.action_disjoint (0 : Fin 2) (1 : Fin 2) (by decide)
  rw [h0, h1] at hd
  exact (Set.disjoint_left.mp hd)
    (Set.mem_univ ((false, false) : Y)) (Set.mem_univ _)

/-- A real admissible-component grammar in which singleton patches are
admitted but the same syntactically valid joint block is forbidden. -/
noncomputable def restricted :
    PartitionGrammar (Fin 1) (Fin 1) (Fin 2) where
  atomsOf := fine.atomsOf
  nonempty := fine.nonempty
  disjoint := fine.disjoint
  cover := fine.cover
  allowed := fun D => D ≠ joint
  allowed_empty := by
    simp [joint]

theorem restricted_action_allowed : restricted.allowed actionOnly := by
  simp [restricted, actionOnly, joint]

theorem restricted_update_allowed : restricted.allowed updateOnly := by
  simp [restricted, updateOnly, joint]

theorem restricted_joint_rejected : ¬ restricted.allowed joint := by
  simp [restricted]

/-- B11: no admissible *typed* intervention can be constructed for a
prohibited block with this frozen admission predicate. -/
theorem forbidden_block_has_no_certificate :
    ¬ ∃ D : AllowedBlock restricted, D.components = joint := by
  rintro ⟨D, hD⟩
  have h : ¬ restricted.allowed joint := restricted_joint_rejected
  exact h (hD ▸ D.accepted)

end AdversarialAdmission
end GrammarRobust
end PermanssonResearch
