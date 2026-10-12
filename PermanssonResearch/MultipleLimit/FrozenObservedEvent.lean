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

/-- A path cannot be eventually ALWAYS true and eventually ALWAYS
false for one fixed observed descriptor. This separation is pointwise
and does not depend on any transition kernel. -/
theorem eventuallyObserved_true_false_disjoint (h : Y → Bool) :
    Disjoint (eventuallyObserved h true)
      (eventuallyObserved h false) := by
  apply Set.disjoint_left.mpr
  intro w htrue hfalse
  obtain ⟨N₁, h₁⟩ := htrue
  obtain ⟨N₂, h₂⟩ := hfalse
  have ht := h₁ (max N₁ N₂) (le_max_left _ _)
  have hf := h₂ (max N₁ N₂) (le_max_right _ _)
  exact Bool.true_ne_false (ht.symm.trans hf)

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
  have hset :
      {w : ℕ → Y | EventuallyInClass w C} =
        ⋃ N : ℕ, ⋂ n : ℕ,
          {w : ℕ → Y | N ≤ n → w n ∈ C} := by
    ext w
    simp only [EventuallyInClass, Set.mem_setOf_eq,
      Set.mem_iUnion, Set.mem_iInter]
  rw [hset]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => ?_
  by_cases hn : N ≤ n
  · have heq :
        {w : ℕ → Y | N ≤ n → w n ∈ C} =
          (fun w : ℕ → Y => w n) ⁻¹' C := by
      ext w
      simp [hn]
    rw [heq]
    exact hC.preimage (measurable_pi_apply n)
  · have heq :
        {w : ℕ → Y | N ≤ n → w n ∈ C} = Set.univ := by
      ext w
      simp [hn]
    rw [heq]
    exact MeasurableSet.univ

end FrozenObservedEvent
end MultipleLimit
end PermanssonResearch
