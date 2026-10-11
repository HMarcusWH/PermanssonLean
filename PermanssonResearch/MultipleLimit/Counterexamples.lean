import PermanssonResearch.MultipleLimit.LimitLaws
import Mathlib.Tactic

/-!
# Lane C1 — formal failure of a universal single-target claim

Two disjoint absorbing states produce two different Dirac occupation
limits. A descriptor may collapse them, so observed plurality must be
separated from physical-state plurality.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit

open PermanssonLean.PeriodicExactGR

def absorbingA : Y := (true, false)
def absorbingB : Y := (true, true)

theorem absorbingA_ne_absorbingB : absorbingA ≠ absorbingB := by
  decide

theorem absorbing_limit_laws_distinct :
    terminalLaw absorbingA ≠ terminalLaw absorbingB := by
  intro h
  exact absorbingA_ne_absorbingB (terminalLaw_injective h)

/-- C1: there cannot be a single state-independent probability measure
equal to the trajectory limit in both absorbing destinations. -/
theorem no_universal_terminal_limit :
    ¬ ∃ ν : ProbabilityMeasure Y,
      terminalLaw absorbingA = ν ∧ terminalLaw absorbingB = ν := by
  rintro ⟨ν, ha, hb⟩
  exact absorbing_limit_laws_distinct (ha.trans hb.symm)

/-- C5: the fixed ex-ante descriptor may identify different physical
absorbing states. State-class plurality does not imply observed plurality. -/
def collapsedDescriptor : Y → Bool := fun _ => false

theorem descriptor_collapses_absorbing_classes :
    absorbingA ≠ absorbingB ∧
    collapsedDescriptor absorbingA = collapsedDescriptor absorbingB := by
  exact ⟨absorbingA_ne_absorbingB, rfl⟩

end MultipleLimit
end PermanssonResearch
