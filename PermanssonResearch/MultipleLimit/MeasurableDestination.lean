import PermanssonResearch.MultipleLimit.Counterexamples
import PermanssonLean.Regime.Occupation
import Mathlib.Tactic

/-!
# Lane C1 — measurable random terminal destination on two absorbing classes

A path may end in a or b, uniquely on the good-path event. We pick b as
a total default on bad paths; on the event of eventual absorption the choice
is canonical and unique. Measurability follows from countable intersections
and unions of measurable coordinate events, not a post-hoc unmeasurable
choice function.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonLean.PeriodicExactGR

theorem eventuallyAt_event_measurable (a : Y) :
    MeasurableSet {w : ℕ → Y | EventuallyAt w a} := by
  have hunion :
      {w : ℕ → Y | EventuallyAt w a} =
        ⋃ N : ℕ, {w : ℕ → Y | ∀ n : ℕ, N ≤ n → w n = a} := by
    ext w
    simp [EventuallyAt]
  rw [hunion]
  apply MeasurableSet.iUnion
  intro N
  have hinter :
      {w : ℕ → Y | ∀ n : ℕ, N ≤ n → w n = a} =
        ⋂ n : ℕ, (if N ≤ n then {w : ℕ → Y | w n = a} else Set.univ) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hw n
      by_cases h : N ≤ n
      · simp [h, hw n h]
      · simp [h]
    · intro hw n hn
      have hx := hw n
      simpa [hn] using hx
  rw [hinter]
  apply MeasurableSet.iInter
  intro n
  by_cases hn : N ≤ n
  · simp only [if_pos hn]
    exact (measurableSet_singleton a).preimage (measurable_pi_apply n)
  · simp [hn]

/-- One total measurable endpoint variable, agreeing with the genuine
terminal absorbing destination on all the permitted good paths. -/
noncomputable def terminalDestination (w : ℕ → Y) : Y := by
  classical
  exact if EventuallyAt w absorbingA then absorbingA else absorbingB

theorem measurable_terminalDestination : Measurable terminalDestination := by
  classical
  unfold terminalDestination
  exact Measurable.ite (eventuallyAt_event_measurable absorbingA)
    measurable_const measurable_const

theorem terminalDestination_correct
    (w : ℕ → Y)
    (h : EventuallyAt w absorbingA ∨ EventuallyAt w absorbingB) :
    EventuallyAt w (terminalDestination w) := by
  by_cases ha : EventuallyAt w absorbingA
  · simpa [terminalDestination, ha] using ha
  · have hb : EventuallyAt w absorbingB := h.resolve_left ha
    simpa [terminalDestination, ha] using hb

theorem measurable_randomTerminalLaw :
    Measurable (fun w : ℕ → Y => terminalLaw (terminalDestination w)) := by
  have h : Measurable terminalLaw := Measurable.of_discrete
  exact h.comp measurable_terminalDestination

/-- The law of the measure-valued limit for any specified path probability
distribution; this is an actual probability pushforward, not a barycenter. -/
noncomputable def pathwiseRandomLimitLaw
    (μ : ProbabilityMeasure (ℕ → Y)) :
    ProbabilityMeasure (ProbabilityMeasure Y) :=
  μ.map (fun w => terminalLaw (terminalDestination w))

theorem pathwiseRandomLimitLaw_apply
    (μ : ProbabilityMeasure (ℕ → Y))
    (E : Set (ProbabilityMeasure Y)) (hE : MeasurableSet E) :
    (pathwiseRandomLimitLaw μ).toMeasure E =
      μ.toMeasure {w | terminalLaw (terminalDestination w) ∈ E} := by
  change
    (Measure.map (fun w => terminalLaw (terminalDestination w)) μ.toMeasure) E =
      μ.toMeasure
        ((fun w => terminalLaw (terminalDestination w)) ⁻¹' E)
  exact Measure.map_apply measurable_randomTerminalLaw hE

/-- Actual canonical weak occupation on the original path law,
conditional on almost-sure absorption into the two fixed states.
No weaker replacement convergence mode is used. -/
theorem canonical_random_occupation_limit
    (M : StrategicWorldModel Bool Bool Bool) (μ : ProbabilityMeasure Y)
    (habs : ∀ᵐ w ∂M.pathLaw μ.toMeasure,
      EventuallyAt w absorbingA ∨ EventuallyAt w absorbingB) :
    ∀ᵐ w ∂M.pathLaw μ.toMeasure,
      Tendsto
        (fun n : ℕ => empiricalOccupation spec w
          (n+1) (Nat.succ_pos n))
        atTop (𝓝 (terminalLaw (terminalDestination w))) := by
  filter_upwards [habs] with w hw
  exact occupation_eventually_at w (terminalDestination w)
    (terminalDestination_correct w hw)

end MultipleLimit
end PermanssonResearch
