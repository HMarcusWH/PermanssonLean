import PermanssonResearch.MultiAgent.FeasibleAnchors
import Mathlib.Tactic

/-!
# F-03: genuine finite strict-opponent legal-fibre obstruction

All original states have NONEMPTY legal opponent menus. Two states in one
strict own-key fibre demand opposite Boolean actions. Their fibre intersection
is empty and the original finite existence theorem therefore rules out every
Markov strictly non-reactive opponent mechanism assigning full legal mass.

This is the original typed PlayerTwoMechanism / anchorKey construction.
No reduction to a single sampled history or singleton menu is assumed.
-/

open MeasureTheory ProbabilityTheory Set
namespace PermanssonResearch.MultiAgent.F03ActualInfeasibleAnchor

open PermanssonLean
open PermanssonResearch.MultiAgent
set_option autoImplicit false

abbrev Y := JointState (GameState Unit Bool Unit) Unit
abbrev OwnKey := Unit × Unit

def oldFalse : Y := (((), (false, ())), ())
def oldTrue : Y := (((), (true, ())), ())

def legal (y : Y) : Set Bool := {y.1.2.1}

theorem each_original_menu_nonempty (y : Y) :
    (legal y).Nonempty := by
  exact ⟨y.1.2.1, rfl⟩

theorem both_starts_have_same_original_strict_key :
    anchorKey oldFalse = anchorKey oldTrue := rfl

theorem legal_oldFalse (a : Bool) :
    a ∈ legal oldFalse ↔ a = false := by
  simp [legal, oldFalse]

theorem legal_oldTrue (a : Bool) :
    a ∈ legal oldTrue ↔ a = true := by
  simp [legal, oldTrue]

theorem legal_fibre_empty_at_genuine_key :
    fibreLegal anchorKey legal (((), ()) : OwnKey) = ∅ := by
  ext a
  constructor
  · intro h
    have hf : a = false := (legal_oldFalse a).mp (h oldFalse rfl)
    have ht : a = true := (legal_oldTrue a).mp (h oldTrue rfl)
    simp [hf] at ht
  · intro h
    simp at h

theorem no_feasible_original_strict_anchor :
    ¬ ∃ a : PlayerTwoMechanism Unit Bool Unit Unit Unit Bool,
      IsStrictlyNonReactive a ∧
        ∀ y : Y, a.action y (legal y) = 1 := by
  intro h
  have hf := (exists_feasible_strictAnchor_iff
    (S0 := Unit) (S1 := Bool) (S2 := Unit)
    (X := Unit) (A1 := Unit) (A2 := Bool) legal).mp h
  have hnonempty := hf (((), ()) : OwnKey)
  rw [legal_fibre_empty_at_genuine_key] at hnonempty
  simpa using hnonempty

theorem all_pointwise_menus_nonempty_but_global_anchor_impossible :
    (∀ y : Y, (legal y).Nonempty) ∧
      ¬ ∃ a : PlayerTwoMechanism Unit Bool Unit Unit Unit Bool,
        IsStrictlyNonReactive a ∧
          ∀ y : Y, a.action y (legal y) = 1 := by
  exact ⟨each_original_menu_nonempty, no_feasible_original_strict_anchor⟩

end PermanssonResearch.MultiAgent.F03ActualInfeasibleAnchor
