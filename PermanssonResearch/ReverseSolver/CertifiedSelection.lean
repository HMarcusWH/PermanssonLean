import PermanssonResearch.ReverseSolver.RationalKernel
import Mathlib.Data.List.MinMax

/-!
# D0-B: executable finite-menu selection and formal index/value soundness

Selection uses List.argmax with exact rational order, rather than classical
choice. Ties choose the *first* maximizer in the declared list. A menu is
indexed and nonempty; no unlisted policy is considered.
-/

namespace PermanssonResearch
namespace ReverseSolver

universe uI

/-- A frozen ordered list of candidates represented by certified rational
row-stochastic matrices, for a shared finite state space. -/
structure RationalMatrixMenu (I : Type uI) (n : ℕ) where
  items : List I
  items_nonempty : items ≠ []
  matrix : I → RationalMarkovMatrix n

/-- Exact rational value of a single fixed member. -/
def rationalMemberValue {I : Type uI} {n : ℕ}
    (menu : RationalMatrixMenu I n) (target : RationalHittingTarget n)
    (y : Fin n) (T : ℕ) (i : I) : ℚ :=
  rationalHittingValue (menu.matrix i) target T y

/-- Deterministic argmax; ties retain the first listed candidate. The
nonempty-list fallback is provably never exercised. -/
def selectRationalMember {I : Type uI} {n : ℕ}
    (menu : RationalMatrixMenu I n) (target : RationalHittingTarget n)
    (y : Fin n) (T : ℕ) : I :=
  (menu.items.argmax (rationalMemberValue menu target y T)).getD
    (menu.items.head menu.items_nonempty)

/-- The selected index really belongs to the *complete frozen* menu. -/
theorem selectRationalMember_mem {I : Type uI} {n : ℕ}
    (menu : RationalMatrixMenu I n) (target : RationalHittingTarget n)
    (y : Fin n) (T : ℕ) :
    selectRationalMember menu target y T ∈ menu.items := by
  unfold selectRationalMember
  cases h : menu.items.argmax (rationalMemberValue menu target y T) with
  | none =>
      have hempty := (List.argmax_eq_none).mp h
      exact (menu.items_nonempty hempty).elim
  | some i =>
      simpa [h] using
        (List.argmax_mem (f := rationalMemberValue menu target y T)
          (by simpa [h] : i ∈ menu.items.argmax (rationalMemberValue menu target y T)))

/-- Every listed fixed candidate has no larger exact rational hitting value
than the deterministic selection. -/
theorem selectRationalMember_dominates {I : Type uI} {n : ℕ}
    (menu : RationalMatrixMenu I n) (target : RationalHittingTarget n)
    (y : Fin n) (T : ℕ) (j : I) (hj : j ∈ menu.items) :
    rationalMemberValue menu target y T j ≤
      rationalMemberValue menu target y T
        (selectRationalMember menu target y T) := by
  unfold selectRationalMember
  cases h : menu.items.argmax (rationalMemberValue menu target y T) with
  | none =>
      exact (menu.items_nonempty ((List.argmax_eq_none).mp h)).elim
  | some i =>
      simpa [h] using
        (List.le_of_mem_argmax (f := rationalMemberValue menu target y T)
          hj (by simpa [h] : i ∈ menu.items.argmax (rationalMemberValue menu target y T)))

/-- A zero selected value implies zero for every *listed* candidate.
No claim is made about omitted interventions. -/
theorem all_rational_menu_values_zero {I : Type uI} {n : ℕ}
    (menu : RationalMatrixMenu I n) (target : RationalHittingTarget n)
    (y : Fin n) (T : ℕ)
    (hz : rationalMemberValue menu target y T
      (selectRationalMember menu target y T) = 0) :
    ∀ j ∈ menu.items, rationalMemberValue menu target y T j = 0 := by
  intro j hj
  have hle := selectRationalMember_dominates menu target y T j hj
  have hnonneg :=
    (rationalHittingValue_mem_Icc (menu.matrix j) target T y).1
  dsimp [rationalMemberValue] at hnonneg
  exact le_antisymm (by simpa [hz] using hle) hnonneg

end ReverseSolver
end PermanssonResearch
