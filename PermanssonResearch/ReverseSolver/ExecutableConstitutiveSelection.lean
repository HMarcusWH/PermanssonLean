import PermanssonResearch.ReverseSolver.RationalConstitutiveMargin
import Mathlib.Data.List.MinMax
import Mathlib.Tactic

/-!
# C10 — deterministic exact rational frozen-menu maximin

The objective is max_i min_{x in original B1} effect(i,x), not the
opposite quantifier order and not D0's finite-horizon hitting objective.
Ties use the FIRST candidate in the numerically ordered finite menu.
-/
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- The frozen complete candidate enumeration is explicit and nonempty. -/
def candidateIndices {n menuSize : ℕ}
    (raw : RawInput n menuSize) (_checked : CheckedInput raw) :
    List (Fin menuSize) := List.finRange menuSize

/-- Exact finite maximin selector, no classical choice. -/
def selectBest {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (cert : MenuCertificate n menuSize) : Fin menuSize :=
  ((candidateIndices raw checked).argmax
      (numericalMargin raw checked cert)).getD ⟨0, checked.menuPositive⟩

/-- The maximizing value, exact in ℚ. -/
def bestMargin {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (cert : MenuCertificate n menuSize) : ℚ :=
  numericalMargin raw checked cert (selectBest raw checked cert)

/-- Return ALL ties, not just a favorable one. This function cannot
silently drop a distinct original menu index having identical rows. -/
def optimalIndices {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (cert : MenuCertificate n menuSize) : List (Fin menuSize) :=
  (candidateIndices raw checked).filter fun i =>
    numericalMargin raw checked cert i = bestMargin raw checked cert

/-- All finite menu candidates are bounded above by the chosen maximum. -/
theorem selected_dominates {n menuSize : ℕ}
    (raw : RawInput n menuSize) (checked : CheckedInput raw)
    (cert : MenuCertificate n menuSize) (i : Fin menuSize) :
    numericalMargin raw checked cert i ≤
      numericalMargin raw checked cert (selectBest raw checked cert) := by
  unfold selectBest
  have hmem : i ∈ candidateIndices raw checked := by
    simp [candidateIndices]
  cases h : (candidateIndices raw checked).argmax
      (numericalMargin raw checked cert) with
  | none =>
      have he : candidateIndices raw checked = [] :=
        (List.argmax_eq_none).mp h
      have hn : (candidateIndices raw checked).Nonempty := by
        simp [candidateIndices, checked.menuPositive]
      exact False.elim (hn.ne_nil he)
  | some j =>
      simpa [h] using
        (List.le_of_mem_argmax
          (f := numericalMargin raw checked cert)
          hmem (by simp [h] : j ∈
            (candidateIndices raw checked).argmax
              (numericalMargin raw checked cert)))

end C10
end ReverseSolver
end PermanssonResearch