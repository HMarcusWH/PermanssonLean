import PermanssonResearch.MultipleLimit.TypedEventualHitting
import PermanssonResearch.MultipleLimit.TypedAbsorbingContinuation
import PermanssonResearch.MultipleLimit.TypedAbsorbingKernel
import Mathlib.Tactic

/-!
# Lane C1 — unconditional almost-sure absorption of actual typed model

The two substantive stochastic obligations are discharged separately:
(1) the exact canonical hitting probabilities tend to one for every
initial law, and (2) the genuine alpha/P/U transition-pair law plus
Dirac absorbing rows enforce permanent continuation almost surely.

No hblocks, hstay or habs hypothesis appears in the final theorem.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedAlmostSureAbsorption

open TypedStrategicWitness TypedAbsorbingKernel
open TypedEventualHitting TypedAbsorbingContinuation

/-- Every initial probability law in the genuine four-state strategic
process reaches one of its two absorbing fixed points and remains there
for the rest of its trajectory, almost surely. -/
theorem canonical_almostSureAbsorption (μ : ProbabilityMeasure Y) :
    HasAlmostSureAbsorption family (model.pathLaw μ.toMeasure) := by
  unfold HasAlmostSureAbsorption
  filter_upwards [canonical_eventually_hits_ae μ,
    stays_after_absorbing_ae μ] with w hhit hstay
  rcases hhit with ⟨t, ht⟩
  exact ⟨w t, ht, ⟨t, fun n hn => hstay t ht n hn⟩⟩

/-- The established generic absorption event is precisely the pair of
possible eventual fixed points on this concrete Boolean space. -/
theorem canonical_eventual_a_or_b (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂model.pathLaw μ.toMeasure,
      EventuallyAt w a ∨ EventuallyAt w b := by
  filter_upwards [canonical_almostSureAbsorption μ] with w hw
  obtain ⟨z, hz, hstay⟩ := hw
  simp only [family, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact Or.inl hstay
  · exact Or.inr hstay

end TypedAlmostSureAbsorption
end MultipleLimit
end PermanssonResearch
