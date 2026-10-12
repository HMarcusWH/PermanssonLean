import PermanssonLean.Regime.Assumption41
import PermanssonResearch.MultipleLimit.ExactSixStateRegion
import Mathlib.Tactic

/-!
# C53-16 — exact Lean adversarial boundaries

These are unconditional NEGATIVE statements about genuinely overstrong
claims. They use the original frozen Assumption 4.1 definition and the
six-state matrix's exact invariant candidates. No stochastic convergence
claim is inferred from finite matrix arithmetic.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace RecurrentCounterexamples

open PermanssonLean
open PermanssonLean.RegimeSpecification
open ExactSixState

/-- A one-state regime can have a perfectly good stationary empirical
measure, but no fixed descriptor can attain two distinct values on it. -/
theorem no_descriptor_two_values_of_subsingleton
    {Y H : Type*} [Subsingleton Y]
    (region : Set Y) (descriptor : Y → H) :
    ¬ ∃ y₁ ∈ region, ∃ y₂ ∈ region,
      descriptor y₁ ≠ descriptor y₂ := by
  rintro ⟨y₁, hy₁, y₂, hy₂, hne⟩
  exact hne (congrArg descriptor (Subsingleton.elim y₁ y₂))

/-- Counterexample gate, expressed using the UNCHANGED original
Assumption 4.1 rather than a weaker research-only definition. -/
theorem no_original_assumption41_of_subsingleton
    {S X A H : Type*}
    [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace A] [MeasurableSpace H]
    [TopologicalSpace S] [TopologicalSpace X]
    [Subsingleton (JointState S X)]
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (reference : MeasureTheory.Measure (JointState S X)) :
    ¬ Assumption41 M spec reference := by
  intro h
  exact no_descriptor_two_values_of_subsingleton
    spec.region spec.descriptor h.2.2.1

/-- The two explicitly normalized six-state physical stationary
candidate VECTORS are distinct. This does not assert path ergodicity. -/
theorem six_state_physical_candidates_distinct :
    piA ≠ piB := by
  intro h
  have heq := congrArg (fun p : Fin 6 → ℚ => p 2) h
  norm_num [piA, piB] at heq

/-- The same declared nonconstant descriptor identifies both recurrent
supports at the observable level, while the physical candidate laws
remain provably different. -/
theorem six_state_distinct_physical_collapsed_observed :
    piA ≠ piB ∧
      (∀ i ∈ classA, observedRecurrent i = true) ∧
      (∀ i ∈ classB, observedRecurrent i = true) := by
  exact ⟨six_state_physical_candidates_distinct,
    ExactSixStateRegion.recurrent_descriptor_collapse⟩

end RecurrentCounterexamples
end MultipleLimit
end PermanssonResearch
