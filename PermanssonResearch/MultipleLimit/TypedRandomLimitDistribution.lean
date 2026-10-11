import PermanssonResearch.MultipleLimit.TypedTerminalMixture
import PermanssonResearch.MultipleLimit.MeasurableDestination
import Mathlib.Tactic

/-!
# Lane C1 — exact two-atom distribution on the space of probability measures

The almost-sure weak empirical occupation limit is a random Dirac measure.
This file states an actual equality of measures on the measure-valued
outcome space; it never identifies the pathwise limit with its barycenter.
The entire result is derived from the genuine canonical alpha/P/U path law.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedRandomLimitDistribution

open TypedStrategicWitness TypedTerminalMixture

noncomputable section

noncomputable def canonicalPathProbability
    (μ : ProbabilityMeasure Y) : ProbabilityMeasure (ℕ → Y) :=
  ⟨model.pathLaw μ.toMeasure, inferInstance⟩

/-- The total random terminal selector takes only one of the two declared
absorbing points, even on exceptional paths (where b is a measurable default). -/
theorem terminalDestination_range (w : ℕ → Y) :
    terminalDestination w = a ∨ terminalDestination w = b := by
  by_cases h : EventuallyAt w absorbingA
  · left
    change (if EventuallyAt w absorbingA then absorbingA else absorbingB) = a
    rw [if_pos h]
    rfl
  · right
    change (if EventuallyAt w absorbingA then absorbingA else absorbingB) = b
    rw [if_neg h]
    rfl

/-- The two terminal events partition the complete canonical path space.
This is a statement about the measurable terminal-selector function. -/
theorem terminalEvents_complement :
    {w : ℕ → Y | terminalDestination w = b} =
      {w : ℕ → Y | terminalDestination w = a}ᶜ := by
  ext w
  rcases terminalDestination_range w with ha | hb
  · have hab : a ≠ b := by decide
    simp [ha, hab]
  · have hba : b ≠ a := by decide
    simp [hb, hba]

/-- Full law of the random terminal *probability measure*. Both weights
are genuine infinite path-event probabilities, not surrogate matrix rows. -/
theorem complete_random_limit_law (μ : ProbabilityMeasure Y) :
    (pathwiseRandomLimitLaw (canonicalPathProbability μ)).toMeasure =
      (model.pathLaw μ.toMeasure
        {w : ℕ → Y | terminalDestination w = a}) •
          Measure.dirac (terminalLaw a) +
      (model.pathLaw μ.toMeasure
        {w : ℕ → Y | terminalDestination w = b}) •
          Measure.dirac (terminalLaw b) := by
  classical
  let P : Measure (ℕ → Y) := model.pathLaw μ.toMeasure
  let EA : Set (ℕ → Y) := {w | terminalDestination w = a}
  let EB : Set (ℕ → Y) := {w | terminalDestination w = b}
  have hEA : MeasurableSet EA :=
    (measurableSet_singleton a).preimage measurable_terminalDestination
  have hsum : P EA + P EB = 1 := by
    have hc : EB = EAᶜ := terminalEvents_complement
    rw [hc]
    have hh : P (EA ∪ EAᶜ) = P EA + P EAᶜ :=
      measure_union (disjoint_compl_right : Disjoint EA EAᶜ) hEA.compl
    calc
      P EA + P EAᶜ = P (EA ∪ EAᶜ) := hh.symm
      _ = 1 := by simp [P]
  apply Measure.ext
  intro E hE
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hE, Measure.dirac_apply' _ hE]
  rw [pathwiseRandomLimitLaw_apply (canonicalPathProbability μ) E hE]
  change P {w : ℕ → Y | terminalLaw (terminalDestination w) ∈ E} =
    (P EA) * (if terminalLaw a ∈ E then 1 else 0) +
    (P EB) * (if terminalLaw b ∈ E then 1 else 0)
  by_cases ha : terminalLaw a ∈ E
  · by_cases hb : terminalLaw b ∈ E
    · have hp : {w : ℕ → Y | terminalLaw (terminalDestination w) ∈ E} =
          Set.univ := by
        ext w
        rcases terminalDestination_range w with hw | hw
        · simp [hw, ha]
        · simp [hw, hb]
      rw [hp, measure_univ]
      simpa [ha, hb, P] using hsum.symm
    · have hp : {w : ℕ → Y | terminalLaw (terminalDestination w) ∈ E} =
          EA := by
        ext w
        rcases terminalDestination_range w with hw | hw
        · simp [EA, hw, ha]
        · have hne : b ≠ a := by decide
          simp [EA, hw, hb, hne]
      rw [hp]
      simp [ha, hb]
  · by_cases hb : terminalLaw b ∈ E
    · have hp : {w : ℕ → Y | terminalLaw (terminalDestination w) ∈ E} =
          EB := by
        ext w
        rcases terminalDestination_range w with hw | hw
        · have hne : a ≠ b := by decide
          simp [EB, hw, ha, hne]
        · simp [EB, hw, hb]
      rw [hp]
      simp [ha, hb]
    · have hp : {w : ℕ → Y | terminalLaw (terminalDestination w) ∈ E} =
          ∅ := by
        ext w
        rcases terminalDestination_range w with hw | hw
        · simp [hw, ha]
        · simp [hw, hb]
      rw [hp, measure_empty]
      simp [ha, hb]

/-- Closed-form law: the pathwise limiting occupation is either delta_a
or delta_b; its law on measures has the exact arbitrary-initial weights. -/
theorem complete_random_limit_law_closed (μ : ProbabilityMeasure Y) :
    (pathwiseRandomLimitLaw (canonicalPathProbability μ)).toMeasure =
      (μ.toMeasure {a} +
        (μ.toMeasure {t} + μ.toMeasure {u}) * (1/3 : ℝ≥0∞)) •
          Measure.dirac (terminalLaw a) +
      (μ.toMeasure {b} +
        (μ.toMeasure {t} + μ.toMeasure {u}) * (2/3 : ℝ≥0∞)) •
          Measure.dirac (terminalLaw b) := by
  rw [complete_random_limit_law, terminal_a_weight_closed, terminal_b_weight_closed]

end
end TypedRandomLimitDistribution
end MultipleLimit
end PermanssonResearch
