import PermanssonResearch.MultipleLimit.CanonicalClassWeights
import PermanssonResearch.MultipleLimit.FiniteEventuallyObserved
import PermanssonLean.Regime.Property
import Mathlib.Tactic

/-!
# C6 — one model-independent asymptotic descriptor event

The SAME event is evaluated on baseline and intervened infinite paths.
It is NOT defined from either model's recurrent-class selector, and it
retains the original time-zero-inclusive infinite-path semantics.
This module proves measurability and the generic path-law probability
functional. The canonical finite-chain occupation theorem is reused.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FrozenObservedEvent

open PermanssonLean
open FiniteCanonicalPath
open FiniteEventuallyObserved
open CanonicalClassWeights
open CanonicalRecurrentResidence
open CanonicalClassSelector
open KernelCommunication
open RecurrentClassDecomposition

variable {Y : Type*} [MeasurableSpace Y]

/-- A fixed observed label occurs at ALL sufficiently late times.
The definition uses neither a baseline kernel nor an intervened selector. -/
def eventuallyObserved (h : Y → Bool) (b : Bool) :
    Set (ℕ → Y) :=
  {w | ∃ N : ℕ, ∀ n : ℕ, N ≤ n → h (w n) = b}

theorem eventuallyObserved_measurable
    (h : Y → Bool) (b : Bool) (hh : Measurable h) :
    MeasurableSet (eventuallyObserved h b) := by
  have hset :
      eventuallyObserved h b =
        ⋃ N : ℕ, ⋂ n : ℕ,
          {w : ℕ → Y | N ≤ n → h (w n) = b} := by
    ext w
    simp only [eventuallyObserved, Set.mem_setOf_eq,
      Set.mem_iUnion, Set.mem_iInter]
  rw [hset]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => ?_
  by_cases hn : N ≤ n
  · have heq :
        {w : ℕ → Y | N ≤ n → h (w n) = b} =
          (fun w : ℕ → Y => h (w n)) ⁻¹' ({b} : Set Bool) := by
      ext w
      simp [hn]
    rw [heq]
    exact (measurableSet_singleton b).preimage
      (hh.comp (measurable_pi_apply n))
  · have heq :
        {w : ℕ → Y | N ≤ n → h (w n) = b} = Set.univ := by
      ext w
      simp [hn]
    rw [heq]
    exact MeasurableSet.univ

/-- Property value is the real probability of the SAME fixed Borel
infinite-path event; it does not depend on the model being evaluated. -/
noncomputable def eventuallyObservedProperty
    (h : Y → Bool) (b : Bool) :
    RegimePropertyMap Y ℝ :=
  fun ρ => (ρ.toMeasure (eventuallyObserved h b)).toReal

/-- A canonical full-path event; a fixed label is not silently
identified with the current model's chosen recurrent representative. -/
theorem eventuallyObserved_iff
    (h : Y → Bool) (b : Bool) (w : ℕ → Y) :
    w ∈ eventuallyObserved h b ↔
      ∃ N : ℕ, ∀ n ≥ N, h (w n) = b := Iff.rfl

/-- A canonical chain whose ALL recurrent states bear one frozen label
satisfies the corresponding event a.s., for every initial law.
This reuses C2's proved recurrent entry and continuation, not a new
strong law or finite-horizon sampling statement. -/
theorem canonical_eventually_observed_ae
    [Fintype Y] [MeasurableSingletonClass Y] [Nonempty Y]
    (K : Kernel Y Y) [IsMarkovKernel K]
    (h : Y → Bool) (hrec : ∀ y ∈ RecurrentStates K, h y = true)
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      w ∈ eventuallyObserved h true := by
  filter_upwards [canonical_descriptor_eventually_true K h hrec μ]
    with w hw
  exact hw

/-- Eventual class residence uses the same measurable countable-event
construction; this is not a statement about arbitrary null paths. -/
theorem eventuallyInClass_measurable
    (C : Set Y) (hC : MeasurableSet C) :
    MeasurableSet
      {w : ℕ → Y | EventuallyInClass w C} := by
  let h : Y → Bool := fun y => decide (y ∈ C)
  classical
  have hh : Measurable h := by
    apply Measurable.of_discrete
  have hset :
      {w : ℕ → Y | EventuallyInClass w C} =
        eventuallyObserved h true := by
    ext w
    simp only [CanonicalRecurrentResidence.EventuallyInClass,
      eventuallyObserved, Set.mem_setOf_eq]
    simp [h]
  rw [hset]
  exact eventuallyObserved_measurable h true hh

end FrozenObservedEvent
end MultipleLimit
end PermanssonResearch
