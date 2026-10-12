import PermanssonResearch.MultipleLimit.KernelCanonicalBlockBridge
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-!
# Lane C2 — generic geometric no-hit tail implies a.s. finite entry

A geometric bound on TRUE measurable path-space no-hit events implies
that the actual infinite trajectory hits the specified target at some
finite index a.s. The proof is general in the measurable state type,
initial path measure and target set. No "independent blocks" argument
is introduced.

The bound itself must be DERIVED from an actual kernel, real canonical
marginals and the fixed-chain uniform N-step entry theorem elsewhere.
This helper alone is not an unconditional recurrent-entry certificate.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace GenericNoHitNull

open KernelCanonicalBlockBridge

variable {Y : Type*} [MeasurableSpace Y]

def NeverHit (A : Set Y) : Set (ℕ → Y) :=
  {w | ∀ n : ℕ, w n ∉ A}

/-- Geometric decay of authentic no-hit probabilities forces the
path-space measure of perpetual avoidance to vanish. -/
theorem neverHit_null_of_geometric
    (P : Measure (ℕ → Y)) (A : Set Y)
    (N : ℕ) (q : ℝ≥0∞) (hq : q < 1)
    (hbound : ∀ k : ℕ,
      P (noHitThrough A (k*N)) ≤ q ^ k) :
    P (NeverHit A) = 0 := by
  have hle (k : ℕ) : P (NeverHit A) ≤ q ^ k := by
    have hsub : NeverHit A ⊆ noHitThrough A (k*N) := by
      intro w hw t ht
      exact hw t
    exact (measure_mono hsub).trans (hbound k)
  apply le_antisymm ?_ bot_le
  exact ge_of_tendsto
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
    (Filter.Eventually.of_forall hle)

/-- A genuine a.s. hitting statement, rather than the much weaker
existence of a graph path from every state. -/
theorem ae_eventually_hits_of_geometric
    (P : Measure (ℕ → Y)) (A : Set Y)
    (N : ℕ) (q : ℝ≥0∞) (hq : q < 1)
    (hbound : ∀ k : ℕ,
      P (noHitThrough A (k*N)) ≤ q ^ k) :
    ∀ᵐ w ∂P, ∃ n : ℕ, w n ∈ A := by
  rw [ae_iff]
  simpa only [NeverHit, not_exists, not_not] using
    neverHit_null_of_geometric P A N q hq hbound

end GenericNoHitNull
end MultipleLimit
end PermanssonResearch
