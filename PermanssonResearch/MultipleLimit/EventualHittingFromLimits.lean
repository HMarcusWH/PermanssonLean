import PermanssonResearch.MultipleLimit.AbsorptionFromTail
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Lane C1 — finite-horizon success approaching one forces eventual hitting

This generic finite-measure argument connects proven canonical finite
hitting-event probabilities with a null event of never hitting. It requires
only actual measurable events and convergence of their real measure to 1,
not an assumed independence property or geometric path-space premise.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace EventualHittingFromLimits

/-- A probability-one limiting family of measurable finite-horizon success
events leaves zero measure for any paths that avoid every success event.
Monotonicity of the event family is not needed for this implication. -/
theorem null_of_success_probability_tendsto_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Set Ω) (E : ℕ → Set Ω)
    (hE : ∀ T, MeasurableSet (E T))
    (hdisjoint : ∀ T, D ⊆ (E T)ᶜ)
    (hlimit : Tendsto (fun T : ℕ => μ.real (E T))
      atTop (𝓝 (1 : ℝ))) :
    μ D = 0 := by
  have hle (T : ℕ) :
      μ.real D ≤ 1 - μ.real (E T) := by
    calc
      μ.real D ≤ μ.real (E T)ᶜ := measureReal_mono (hdisjoint T)
      _ = μ.real Set.univ - μ.real (E T) := measureReal_compl (hE T)
      _ = 1 - μ.real (E T) := by simp
  have hzero : Tendsto (fun T : ℕ => 1 - μ.real (E T))
      atTop (𝓝 (0 : ℝ)) := by
    convert tendsto_const_nhds.sub hlimit using 1 <;> norm_num
  have hnonpos : μ.real D ≤ 0 :=
    ge_of_tendsto hzero (Filter.Eventually.of_forall hle)
  have hreal : μ.real D = 0 :=
    le_antisymm hnonpos measureReal_nonneg
  have hfinite : μ D ≠ ∞ := measure_ne_top μ D
  have hconvert := ENNReal.ofReal_toReal hfinite
  simpa [Measure.real, hreal] using hconvert.symm

end EventualHittingFromLimits
end MultipleLimit
end PermanssonResearch
