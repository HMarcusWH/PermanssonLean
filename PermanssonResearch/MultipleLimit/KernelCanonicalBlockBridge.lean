import PermanssonResearch.MultipleLimit.KernelBlockSurvival
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Tactic

/-!
# Lane C1 — generic kernel-power → canonical no-hit path-space bridge

Pathwise surviving an absorbing-set avoidance test through time n
implies the endpoint at n remains outside the set. Hence the canonical
no-hit probability is bounded by the time-n marginal, and genuine
Chapman–Kolmogorov kernel powers yield geometric N-block survival.

This theorem assumes the authentic time-marginal identity and an
explicit uniform N-step kernel bound. For the typed witness the former
is proved separately by TypedMarginalPowers; no independence premise
or fabricated path measure appears.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace KernelCanonicalBlockBridge

open KernelBlockSurvival

def noHitThrough {Y : Type*} (A : Set Y) (n : ℕ) : Set (ℕ → Y) :=
  {w | ∀ t : ℕ, t ≤ n → w t ∉ A}

/-- A no-hit prefix is contained in the measurable event that its last
coordinate remains outside the absorbing set. -/
theorem noHitThrough_subset_endpoint
    {Y : Type*} (A : Set Y) (n : ℕ) :
    noHitThrough A n ⊆
      (fun w : ℕ → Y => w n) ⁻¹' Aᶜ := by
  intro w hw
  exact hw n le_rfl

/-- A real infinite path law with time marginals equal to powers of its
true Markov kernel inherits the uniform N-block geometric no-hit bound
from the actual kernel's Chapman–Kolmogorov bound. -/
theorem canonical_geometric_noHit
    {Y : Type*} [MeasurableSpace Y]
    (K : Kernel Y Y) (P : Measure (ℕ → Y)) (y : Y)
    (A : Set Y) (hA : MeasurableSet A)
    (hMarginal : ∀ n : ℕ,
      P.map (fun w : ℕ → Y => w n) = (K ^ n) y)
    (N : ℕ) (q : ℝ≥0∞)
    (hinside : ∀ z ∈ A, (K ^ N) z Aᶜ = 0)
    (houtside : ∀ z ∉ A, (K ^ N) z Aᶜ ≤ q) :
    ∀ k : ℕ,
      P (noHitThrough A (k*N)) ≤ q^k := by
  intro k
  have hmeas : Measurable (fun w : ℕ → Y => w (k*N)) :=
    measurable_pi_apply _
  calc
    P (noHitThrough A (k*N)) ≤
        P ((fun w : ℕ → Y => w (k*N)) ⁻¹' Aᶜ) :=
      measure_mono (noHitThrough_subset_endpoint A (k*N))
    _ = (K ^ (k*N)) y Aᶜ := by
      rw [← hMarginal (k*N)]
      exact (Measure.map_apply hmeas hA.compl).symm
    _ ≤ q^k :=
      geometric_endpoint_power_of_absorbing_block
        K A hA N q hinside houtside k y

end KernelCanonicalBlockBridge
end MultipleLimit
end PermanssonResearch
