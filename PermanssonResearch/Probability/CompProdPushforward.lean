import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

/-!
# Pushing the first factor of a measure–kernel composition

Low-level generic lemma shared by C-Exit D (C69, shifted-prefix stationarity)
and E1 (approximate quotients). Extracted here so that neither lane imports
the other; arbitrary measurable spaces, no standard-Borel hypothesis.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace PermanssonResearch.Probability

set_option autoImplicit false

/-- Pushing the FIRST factor of a measure–kernel composition forward along
`f` is the same as composing with the kernel read through `f` and then
pushing the pair forward. -/
theorem compProd_map_left_eq_map_compProd_comap
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ]
    (ρ : Measure α) [IsFiniteMeasure ρ]
    {f : α → β} (hf : Measurable f)
    (η : Kernel β γ) [IsMarkovKernel η] :
    (ρ.map f) ⊗ₘ η = (ρ ⊗ₘ η.comap f hf).map (Prod.map f id) := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (hf.prodMap measurable_id) (hs.prod ht)]
  have hpre : Prod.map f id ⁻¹' (s ×ˢ t) = (f ⁻¹' s) ×ˢ t := by
    ext ⟨a, c⟩
    simp
  rw [hpre, Measure.compProd_apply_prod hs ht,
    Measure.compProd_apply_prod (hf hs) ht,
    setLIntegral_map hs (η.measurable_coe ht) hf]
  rfl

end PermanssonResearch.Probability
