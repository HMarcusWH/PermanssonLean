import PermanssonResearch.ReverseSolver.RationalKernel
import Mathlib.Tactic

/-!
# C10 — finite exact-rational checked input reflection

This module validates a *typed raw array/function representation*. Parsing
external bytes/JSON into these functions is outside the Lean proof boundary.
Successful validation constructs proof-carrying, exact rational Markov rows;
there is no rounding and no silently accepted zero-state/menu universe.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- A complete but untrusted finite rational input, before its stochasticity
and nonempty comparison witnesses have been checked. -/
structure RawInput (n menuSize : ℕ) where
  baseline : Fin n → Fin n → ℚ
  members : Fin menuSize → Fin n → Fin n → ℚ
  descriptor : Fin n → Bool
  comparison : Finset (Fin n)

/-- A successful check retains the raw input and an *entrywise* proof that
the accepted stochastic matrices are precisely the input entries. -/
structure CheckedInput {n menuSize : ℕ} (raw : RawInput n menuSize) where
  statesPositive : 0 < n
  menuPositive : 0 < menuSize
  comparisonNonempty : raw.comparison.Nonempty
  baseline : RationalMarkovMatrix n
  members : Fin menuSize → RationalMarkovMatrix n
  baselineExact : ∀ x y, baseline.entry x y = raw.baseline x y
  membersExact : ∀ i x y, (members i).entry x y = raw.members i x y

/-- All finite proofs are decided on exact ℚ values; the conditional casts
are genuine stochasticity evidence, never a user-supplied status flag. -/
def validateInput {n menuSize : ℕ} (raw : RawInput n menuSize) :
    Option (CheckedInput raw) :=
  if hn : 0 < n then
    if hm : 0 < menuSize then
      if hc : raw.comparison.Nonempty then
        if hb0 : ∀ x y : Fin n, 0 ≤ raw.baseline x y then
          if hb1 : ∀ x : Fin n, (∑ y : Fin n, raw.baseline x y) = 1 then
            if hs0 : ∀ i : Fin menuSize, ∀ x y : Fin n,
                0 ≤ raw.members i x y then
              if hs1 : ∀ i : Fin menuSize, ∀ x : Fin n,
                  (∑ y : Fin n, raw.members i x y) = 1 then
                some {
                  statesPositive := hn
                  menuPositive := hm
                  comparisonNonempty := hc
                  baseline := {
                    entry := raw.baseline
                    entry_nonneg := hb0
                    row_sum_one := hb1
                  }
                  members := fun i => {
                    entry := raw.members i
                    entry_nonneg := hs0 i
                    row_sum_one := hs1 i
                  }
                  baselineExact := by intro x y; rfl
                  membersExact := by intro i x y; rfl
                }
              else none
            else none
          else none
        else none
      else none
    else none
  else none

/-- An accepted value certifies the exact numerical input; no separate
stochasticity assumptions are passed to an evaluator. -/
theorem checked_baseline_exact {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (x y : Fin n) :
    checked.baseline.entry x y = raw.baseline x y :=
  checked.baselineExact x y

theorem checked_member_exact {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (i : Fin menuSize) (x y : Fin n) :
    (checked.members i).entry x y = raw.members i x y :=
  checked.membersExact i x y

/-- The admitted finite state/menu dimensions cannot be vacuous. -/
theorem accepted_dimensions_positive {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw) :
    0 < n ∧ 0 < menuSize ∧ raw.comparison.Nonempty :=
  ⟨checked.statesPositive, checked.menuPositive,
    checked.comparisonNonempty⟩

end C10
end ReverseSolver
end PermanssonResearch