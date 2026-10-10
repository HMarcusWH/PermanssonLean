import PermanssonResearch.MultipleLimit.AbsorptionTail
import PermanssonLean.Examples.PeriodicExactGR
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-!
# Lane C1 — canonical measurable hitting from an established geometric tail

This theorem converts a genuine measure bound on every N-block no-hit event
to an almost-sure finite hitting event; no independence is assumed.
It does not derive the bound from the Markov kernel (a separate bridge).
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace PermanssonResearch
namespace MultipleLimit

open PermanssonLean.PeriodicExactGR

def NoHitThrough (A : Finset Y) (T : ℕ) : Set (ℕ → Y) :=
  {w | ∀ t : ℕ, t ≤ T → w t ∉ A}

def NeverHit (A : Finset Y) : Set (ℕ → Y) :=
  {w | ∀ t : ℕ, w t ∉ A}

theorem neverHit_measurable (A : Finset Y) :
    MeasurableSet (NeverHit A) := by
  have heq : NeverHit A = ⋂ t : ℕ, {w : ℕ → Y | w t ∉ A} := by
    ext w
    simp [NeverHit]
  rw [heq]
  apply MeasurableSet.iInter
  intro t
  exact (MeasurableSet.of_discrete : MeasurableSet (A : Set Y)).compl.preimage
    (measurable_pi_apply t)

/-- If the exact canonical no-hit probabilities have a uniform geometric
upper bound at horizon kN, the actual measure of never hitting is zero.
No claim of a kernel-derived bound is smuggled into the hypothesis. -/
theorem neverHit_null_of_geometric_bounds
    (μ : Measure (ℕ → Y)) (A : Finset Y)
    (N : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hblocks : ∀ k : ℕ,
      μ (NoHitThrough A (k*N)) ≤ ENNReal.ofReal ((1-ε)^k)) :
    μ (NeverHit A) = 0 := by
  have hq0 : 0 ≤ 1-ε := by linarith
  have hq1 : 1-ε < 1 := by linarith
  have hp : Tendsto (fun k : ℕ => (1-ε)^k) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hlimit : Tendsto (fun k : ℕ => ENNReal.ofReal ((1-ε)^k))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa using ENNReal.tendsto_ofReal hp
  have hle (k : ℕ) : μ (NeverHit A) ≤ ENNReal.ofReal ((1-ε)^k) := by
    have hsub : NeverHit A ⊆ NoHitThrough A (k*N) := by
      intro w hw t _
      exact hw t
    exact (measure_mono hsub).trans (hblocks k)
  apply le_antisymm ?_ zero_le
  exact ge_of_tendsto hlimit (Filter.Eventually.of_forall hle)

/-- Canonical almost-sure finite hitting, conditioned on an actual no-hit
bound rather than a false assumption of independence of time blocks. -/
theorem ae_eventually_hits_of_geometric_bounds
    (μ : Measure (ℕ → Y)) (A : Finset Y)
    (N : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hblocks : ∀ k : ℕ,
      μ (NoHitThrough A (k*N)) ≤ ENNReal.ofReal ((1-ε)^k)) :
    ∀ᵐ w ∂μ, ∃ t : ℕ, w t ∈ A := by
  rw [ae_iff]
  simpa only [NeverHit, not_exists, not_not] using
    neverHit_null_of_geometric_bounds μ A N ε hε0 hε1 hblocks


/-- Once the canonical path law also satisfies the fixed-point continuation
rule after entering the absorbing set, geometric hitting becomes genuine
almost-sure *eventual constancy*. The continuation premise is independently
required here and must ultimately follow from the actual Markov transition
kernel's absorbing-row identity. -/
theorem ae_absorptionPaths_of_geometric_bounds
    (F : AbsorbingFamily Y) (μ : Measure (ℕ → Y))
    (N : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hblocks : ∀ k : ℕ,
      μ (NoHitThrough F.absorbing (k*N)) ≤ ENNReal.ofReal ((1-ε)^k))
    (hstay : ∀ᵐ w ∂μ,
      ∀ t : ℕ, w t ∈ F.absorbing →
        ∀ n : ℕ, t ≤ n → w n = w t) :
    HasAlmostSureAbsorption F μ := by
  unfold HasAlmostSureAbsorption
  filter_upwards [ae_eventually_hits_of_geometric_bounds μ
      F.absorbing N ε hε0 hε1 hblocks, hstay] with w hw hs
  obtain ⟨t, ht⟩ := hw
  exact ⟨w t, ht, ⟨t, fun n hn => hs t ht n hn⟩⟩

end MultipleLimit
end PermanssonResearch
