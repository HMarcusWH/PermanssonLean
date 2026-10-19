import PermanssonResearch.X1.ExactMargins
import Mathlib.Tactic

/-!
NEXT-03 / X-04: an actual omitted equilibrium tied start.

All nine original comparison starts attain the same equilibrium/action effect.
Removing one start can leave the numerical infimum unchanged, but cannot
preserve the FULL original comparison domain. This is a theorem about the
actual supplied X1 property, not a numerical stand-in or an Exact GR claim.
-/

namespace PermanssonResearch.X1.TiedStartDomain

open PermanssonResearch.X1

set_option autoImplicit false

def omittedTiedStart : Set Y :=
  {y | y ∈ comparisonStarts ∧ y ≠ y0}

theorem y0_in_original : y0 ∈ comparisonStarts := by rfl

theorem y0_absent_from_omitted : y0 ∉ omittedTiedStart := by
  intro hy
  exact hy.2 rfl

theorem remaining_start_nonempty :
    (((0, 0), true) : Y) ∈ omittedTiedStart := by
  constructor
  · rfl
  · decide

/-- The equality of nine finite effects is proved in the actual X1 tables. -/
theorem all_original_equilibrium_action_starts_tie (y : Y)
    (hy : y ∈ comparisonStarts) :
    exactEffect false .action y = exactMargin false .action := by
  exact (exactEffect_attainers false .action y hy).2 (Or.inl rfl)

/-- The omitted domain still has exactly the same NUMERICAL infimum. -/
theorem omitted_domain_same_numeric_inf :
    sInf (exactEffect false .action '' omittedTiedStart) =
      exactMargin false .action := by
  have heq : exactEffect false .action '' omittedTiedStart =
      {exactMargin false .action} := by
    ext a
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Set.mem_singleton_iff.mpr
        (all_original_equilibrium_action_starts_tie y hy.1)
    · intro ha
      have h : a = exactMargin false .action := by simpa using ha
      subst a
      exact ⟨((0, 0), true), remaining_start_nonempty,
        all_original_equilibrium_action_starts_tie _ remaining_start_nonempty.1⟩
  simpa [heq]

/-- Same infimum is NOT equality of the original constitutive-comparison set. -/
theorem omitted_domain_not_original :
    omittedTiedStart ≠ comparisonStarts := by
  intro heq
  exact y0_absent_from_omitted (heq.symm ▸ y0_in_original)

theorem false_full_domain_coverage_rejected :
    ¬ (∀ y ∈ comparisonStarts, y ∈ omittedTiedStart) := by
  intro hall
  exact y0_absent_from_omitted (hall y0 y0_in_original)

end PermanssonResearch.X1.TiedStartDomain
